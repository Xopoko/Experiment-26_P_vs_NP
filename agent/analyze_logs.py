#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


_ROLE_HEADER_RE = re.compile(r"^====\s+(WORKER|SKEPTIC|SUPERVISOR)\s+round=(\d+)\s+")
_COMMIT_RE = re.compile(r"^\[([^\]]+)\s+([0-9a-f]{7,})\]\s+(.*)$")
_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")


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

    role_sections: dict[str, int] = {"WORKER": 0, "SKEPTIC": 0, "SUPERVISOR": 0}
    role_commits: dict[str, list[Commit]] = {"WORKER": [], "SKEPTIC": [], "SUPERVISOR": []}
    commits: list[Commit] = []

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

        lower = line.lower()
        if "traceback (most recent call last)" in lower or "assertionerror" in lower:
            errors.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
            continue
        if lower.startswith("error:") or " error:" in lower:
            errors.append({"line": idx, "role": current_role, "round": current_round, "text": line.strip()})
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
    dup = summary.get("duplicate_step_ids") or []
    errs = summary.get("errors") or []

    print(f"Log: {log_path}")
    print(f"run_id: {run_id}  mode: {mode}  started_at: {started}")
    if rounds:
        print(f"rounds: {len(rounds)} ({', '.join(str(r) for r in rounds)})")
    else:
        print("rounds: 0")
    print(
        "sections:"
        f" WORKER={sections.get('WORKER', 0)}"
        f" SKEPTIC={sections.get('SKEPTIC', 0)}"
        f" SUPERVISOR={sections.get('SUPERVISOR', 0)}"
    )
    print(
        "commits:"
        f" total={commits_total}"
        f" WORKER={commits_by_role.get('WORKER', 0)}"
        f" SKEPTIC={commits_by_role.get('SKEPTIC', 0)}"
        f" SUPERVISOR={commits_by_role.get('SUPERVISOR', 0)}"
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

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
