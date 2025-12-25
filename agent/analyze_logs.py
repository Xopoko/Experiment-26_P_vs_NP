#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


_ROLE_HEADER_RE = re.compile(r"^====\s+(QUESTION_SETTER|WORKER|SKEPTIC|SUPERVISOR)\s+round=(\d+)\s+")
_COMMIT_RE = re.compile(r"^\[([^\]]+)\s+([0-9a-f]{7,})\]\s+(.*)$")
_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")
_SHELL_OK_RE = re.compile(r"^/bin/bash -lc (.*) in .* succeeded\b")
_REPORTED_STEP_ID_RE = re.compile(r"\bStepID\b\s*[:=]\s*(Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?)")
_REPORTED_INFOGAIN_RE = re.compile(r"\bInfoGain\b\s*[:=]\s*([012])\b")


@dataclass(frozen=True)
class Commit:
    role: str | None
    round: int | None
    sha: str
    message: str
    step_id: str | None
    line_no: int


def _pick_log_file(*, root: Path, mode: str | None, explicit: str | None) -> Path:
    if explicit:
        return (root / explicit).resolve() if not Path(explicit).is_absolute() else Path(explicit)

    logs = root / "agent" / "logs"
    candidates: list[Path] = []
    if mode in (None, "trio"):
        candidates.append(logs / "latest_trio.log")
    if mode in (None, "duo"):
        candidates.append(logs / "latest_duo.log")
    if mode in (None, "single"):
        candidates.append(logs / "latest.log")

    for p in candidates:
        if p.exists():
            return p
    raise FileNotFoundError(
        "no log file found (tried: "
        + ", ".join(str(p) for p in candidates)
        + "); pass --log PATH or run ./agent/run_trio.sh"
    )


def _parse_step_id_from_message(message: str) -> str | None:
    token = message.strip().split()[0] if message.strip() else ""
    token = token.rstrip(":,;.")
    if token and _STEP_ID_RE.match(token):
        return token

    m = re.search(r"Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?", message)
    if m and _STEP_ID_RE.match(m.group(0)):
        return m.group(0)
    return None


def _analyze_log(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()

    meta: dict[str, Any] = {
        "log_file": str(path),
        "run_id": None,
        "mode": None,
        "started_at": None,
        "worker_prompt": None,
        "skeptic_prompt": None,
        "supervisor_prompt": None,
    }

    current_role: str | None = None
    current_round: int | None = None
    rounds_seen: set[int] = set()

    role_sections: dict[str, int] = {"QUESTION_SETTER": 0, "WORKER": 0, "SKEPTIC": 0, "SUPERVISOR": 0}
    role_commits: dict[str, list[Commit]] = {"QUESTION_SETTER": [], "WORKER": [], "SKEPTIC": [], "SUPERVISOR": []}
    commits: list[Commit] = []

    role_cmd_counts: dict[str, dict[str, int]] = {
        "QUESTION_SETTER": {"total": 0, "rg": 0, "rg_text_cache": 0, "verify": 0, "git_commit": 0},
        "WORKER": {"total": 0, "rg": 0, "rg_text_cache": 0, "verify": 0, "git_commit": 0},
        "SKEPTIC": {"total": 0, "rg": 0, "rg_text_cache": 0, "verify": 0, "git_commit": 0},
        "SUPERVISOR": {"total": 0, "rg": 0, "rg_text_cache": 0, "verify": 0, "git_commit": 0},
    }
    role_cmd_last: dict[str, list[str]] = {"QUESTION_SETTER": [], "WORKER": [], "SKEPTIC": [], "SUPERVISOR": []}
    role_mcp_counts: dict[str, int] = {"QUESTION_SETTER": 0, "WORKER": 0, "SKEPTIC": 0, "SUPERVISOR": 0}
    role_reported: dict[str, dict[str, Any]] = {
        "QUESTION_SETTER": {"step_id": None, "step_id_line": None, "infogain": None, "infogain_line": None},
        "WORKER": {"step_id": None, "step_id_line": None, "infogain": None, "infogain_line": None},
        "SKEPTIC": {"step_id": None, "step_id_line": None, "infogain": None, "infogain_line": None},
        "SUPERVISOR": {"step_id": None, "step_id_line": None, "infogain": None, "infogain_line": None},
    }

    errors: list[dict[str, Any]] = []
    warnings: list[dict[str, Any]] = []

    for idx, line in enumerate(lines, start=1):
        if meta["started_at"] is None and line.startswith("---- ") and line.endswith(" ----"):
            meta["started_at"] = line.strip("- ").strip()
            continue

        if line.startswith("run_id:"):
            meta["run_id"] = line.split(":", 1)[1].strip()
            continue
        if line.startswith("mode:"):
            meta["mode"] = line.split(":", 1)[1].strip()
            continue
        if line.startswith("worker_prompt:"):
            meta["worker_prompt"] = line.split(":", 1)[1].strip()
            continue
        if line.startswith("skeptic_prompt:"):
            meta["skeptic_prompt"] = line.split(":", 1)[1].strip()
            continue
        if line.startswith("supervisor_prompt:"):
            meta["supervisor_prompt"] = line.split(":", 1)[1].strip()
            continue

        m = _ROLE_HEADER_RE.match(line)
        if m:
            current_role = m.group(1)
            current_round = int(m.group(2))
            rounds_seen.add(current_round)
            role_sections[current_role] += 1
            continue

        m = _COMMIT_RE.match(line)
        if m:
            _branch = m.group(1)
            sha = m.group(2)
            msg = m.group(3).strip()
            step_id = _parse_step_id_from_message(msg)
            c = Commit(
                role=current_role,
                round=current_round,
                sha=sha,
                message=msg,
                step_id=step_id,
                line_no=idx,
            )
            commits.append(c)
            if current_role in role_commits:
                role_commits[current_role].append(c)
            continue

        m = _SHELL_OK_RE.match(line)
        if m and current_role in role_cmd_counts:
            cmd = m.group(1).strip()
            role_cmd_counts[current_role]["total"] += 1

            # Normalize quoted `-lc "..."` payloads for simple substring checks.
            if (cmd.startswith('"') and cmd.endswith('"')) or (cmd.startswith("'") and cmd.endswith("'")):
                cmd = cmd[1:-1]

            if re.search(r"(^|\s)rg(\s|$)", cmd):
                role_cmd_counts[current_role]["rg"] += 1
                if "resources/text_cache/" in cmd:
                    role_cmd_counts[current_role]["rg_text_cache"] += 1
            if "python3 scripts/verify_notebook.py" in cmd:
                role_cmd_counts[current_role]["verify"] += 1
            if re.search(r"(^|\s)git(\s|$)", cmd) and " commit" in cmd:
                role_cmd_counts[current_role]["git_commit"] += 1

            last = role_cmd_last[current_role]
            last.append(cmd)
            if len(last) > 8:
                del last[0 : len(last) - 8]
            continue

        if current_role in role_reported:
            m = _REPORTED_STEP_ID_RE.search(line)
            if m and _STEP_ID_RE.match(m.group(1)):
                role_reported[current_role]["step_id"] = m.group(1)
                role_reported[current_role]["step_id_line"] = idx
            m = _REPORTED_INFOGAIN_RE.search(line)
            if m:
                role_reported[current_role]["infogain"] = int(m.group(1))
                role_reported[current_role]["infogain_line"] = idx

        if "mcp:" in line and "firecrawl" in line and current_role in role_mcp_counts:
            role_mcp_counts[current_role] += 1

        lower = line.lower()
        if "rg: regex parse error" in lower:
            warnings.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue
        if "traceback (most recent call last)" in lower:
            errors.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue
        if lower.startswith("failed:"):
            errors.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue
        if lower.startswith("error:"):
            warnings.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue
        if "stopping:" in lower and "max_rounds" in lower:
            warnings.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue

    step_ids = [c.step_id for c in commits if c.step_id]
    duplicates = sorted({sid for sid in step_ids if step_ids.count(sid) > 1})

    summary: dict[str, Any] = {
        **meta,
        "rounds": sorted(rounds_seen),
        "sections": {
            "WORKER": role_sections["WORKER"],
            "SKEPTIC": role_sections["SKEPTIC"],
            "SUPERVISOR": role_sections["SUPERVISOR"],
        },
        "commits_total": len(commits),
        "commits_by_role": {k: len(v) for k, v in role_commits.items()},
        "commands_by_role": role_cmd_counts,
        "commands_last_by_role": role_cmd_last,
        "mcp_firecrawl_by_role": role_mcp_counts,
        "reported_by_role": role_reported,
        "step_ids": step_ids,
        "duplicate_step_ids": duplicates,
        "errors": errors,
        "warnings": warnings,
        "commits": [
            {
                "role": c.role,
                "round": c.round,
                "sha": c.sha,
                "message": c.message,
                "step_id": c.step_id,
                "line": c.line_no,
            }
            for c in commits
        ],
    }
    return summary


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Summarize agent runner logs (duo/trio/single).")
    parser.add_argument("--log", default=None, help="Path to a log file (default: latest_{trio,duo}.log).")
    parser.add_argument(
        "--mode",
        choices=["trio", "duo", "single"],
        default=None,
        help="Which latest log symlink to prefer (default: try trio, then duo, then single).",
    )
    parser.add_argument("--json", action="store_true", help="Output machine-readable JSON.")
    args = parser.parse_args(argv)

    root = Path(__file__).resolve().parents[1]
    try:
        log_path = _pick_log_file(root=root, mode=args.mode, explicit=args.log)
    except FileNotFoundError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if not log_path.exists():
        print(f"error: log file not found: {log_path}", file=sys.stderr)
        return 2

    summary = _analyze_log(log_path)

    if args.json:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
        return 0

    mode = summary.get("mode") or "?"
    run_id = summary.get("run_id") or "?"
    started = summary.get("started_at") or "?"
    rounds = summary.get("rounds") or []
    sections = summary.get("sections") or {}
    commits_total = summary.get("commits_total") or 0
    commits_by_role = summary.get("commits_by_role") or {}
    commands_by_role = summary.get("commands_by_role") or {}
    reported_by_role = summary.get("reported_by_role") or {}
    dup = summary.get("duplicate_step_ids") or []
    errs = summary.get("errors") or []
    warns = summary.get("warnings") or []

    print(f"Log: {log_path}")
    print(f"run_id: {run_id}  mode: {mode}  started_at: {started}")
    if rounds:
        print(f"rounds: {len(rounds)} ({', '.join(str(r) for r in rounds)})")
    else:
        print("rounds: 0")
    print(
        "sections:"
        f" QUESTION_SETTER={sections.get('QUESTION_SETTER', 0)}"
        f" WORKER={sections.get('WORKER', 0)}"
        f" SKEPTIC={sections.get('SKEPTIC', 0)}"
        f" SUPERVISOR={sections.get('SUPERVISOR', 0)}"
    )
    print(
        "commits:"
        f" total={commits_total}"
        f" QUESTION_SETTER={commits_by_role.get('QUESTION_SETTER', 0)}"
        f" WORKER={commits_by_role.get('WORKER', 0)}"
        f" SKEPTIC={commits_by_role.get('SKEPTIC', 0)}"
        f" SUPERVISOR={commits_by_role.get('SUPERVISOR', 0)}"
    )
    q_cmd = commands_by_role.get("QUESTION_SETTER") or {}
    w_cmd = commands_by_role.get("WORKER") or {}
    s_cmd = commands_by_role.get("SKEPTIC") or {}
    sup_cmd = commands_by_role.get("SUPERVISOR") or {}
    print(
        "cmds:"
        f" QUESTION_SETTER=({q_cmd.get('total', 0)} total, {q_cmd.get('rg', 0)} rg, {q_cmd.get('rg_text_cache', 0)} rg_text_cache)"
        f" WORKER=({w_cmd.get('total', 0)} total, {w_cmd.get('rg', 0)} rg, {w_cmd.get('rg_text_cache', 0)} rg_text_cache, {w_cmd.get('verify', 0)} verify)"
        f" SKEPTIC=({s_cmd.get('total', 0)} total, {s_cmd.get('rg', 0)} rg, {s_cmd.get('rg_text_cache', 0)} rg_text_cache, {s_cmd.get('verify', 0)} verify)"
        f" SUPERVISOR=({sup_cmd.get('total', 0)} total, {sup_cmd.get('verify', 0)} verify)"
    )
    w_rep = reported_by_role.get("WORKER") or {}
    s_rep = reported_by_role.get("SKEPTIC") or {}
    print(
        "reported:"
        f" WORKER=(StepID={w_rep.get('step_id') or '-'}, InfoGain={w_rep.get('infogain') if w_rep.get('infogain') is not None else '-'})"
        f" SKEPTIC=(StepID={s_rep.get('step_id') or '-'}, InfoGain={s_rep.get('infogain') if s_rep.get('infogain') is not None else '-'})"
    )
    if dup:
        print(f"duplicate StepID(s) in commits: {', '.join(dup)}")

    commits = summary.get("commits") or []
    if commits:
        last = commits[-1]
        print(f"last_commit: {last.get('sha')} {last.get('message')}")

    if errs:
        print(f"errors: {len(errs)} (first at line {errs[0].get('line')})")
    else:
        print("errors: 0")
    if warns:
        print(f"warnings: {len(warns)} (first at line {warns[0].get('line')})")
    else:
        print("warnings: 0")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
