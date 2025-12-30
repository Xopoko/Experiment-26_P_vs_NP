#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import re
import subprocess
import sys
from pathlib import Path


_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")
_ALLOWED_TYPES = {"Proof", "Counterexample", "Exact citation", "Toy", "Reduction", "Barrier"}


def _parse_step_id(value: str) -> str:
    token = value.strip()
    if not token:
        raise ValueError("missing StepID")
    if not _STEP_ID_RE.match(token):
        raise ValueError(f"invalid StepID {token!r} (expected Qxx.Sy.slug)")
    return token


def _git_head() -> str:
    try:
        res = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception as exc:  # noqa: BLE001 - pass through
        raise ValueError(f"failed to resolve git HEAD: {exc}") from exc
    token = res.stdout.strip()
    if not token:
        raise ValueError("git HEAD is empty")
    return token


def _parse_commit(value: str, *, allow_pending: bool, default_to_head: bool) -> str:
    token = value.strip()
    if not token and default_to_head:
        token = _git_head()
    if not token:
        raise ValueError("missing Commit")
    if token == "PENDING":
        if allow_pending:
            return token
        raise ValueError("Commit cannot be PENDING for done artifacts")
    if not re.fullmatch(r"[0-9a-fA-F]{7,40}", token):
        raise ValueError(f"invalid Commit {token!r} (expected hex)")
    return token


def _load_artifacts(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    if not path.exists():
        raise FileNotFoundError(f"missing artifacts log: {path}")
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        headers = list(reader.fieldnames or [])
        rows = [dict(r) for r in reader]
    return headers, rows


def _write_artifacts(path: Path, headers: list[str], rows: list[dict[str, str]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers, delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def _update_agent_brief(
    path: Path,
    *,
    step_id: str,
    info_gain: str,
    approach_tag: str | None = None,
    failure_reason: str | None = None,
) -> None:
    if not path.exists():
        raise FileNotFoundError(f"missing agent brief: {path}")

    lines = path.read_text(encoding="utf-8").splitlines()

    def replace_meta(key: str, new_value: str) -> None:
        needle = f"`{key}:`"
        for i, line in enumerate(lines):
            if needle not in line:
                continue
            prefix, _ = line.split(needle, 1)
            lines[i] = f"{prefix}{needle} {new_value}"
            return
        raise ValueError(f"missing `{key}:` in {path}")

    def update_do_not_repeat(key: str) -> None:
        needle = f"`{key}:`"
        for i, line in enumerate(lines):
            if needle not in line:
                continue
            prefix, rest = line.split(needle, 1)
            existing = [s.strip() for s in rest.split(",") if s.strip()]
            merged: list[str] = [step_id]
            for item in existing:
                if item != step_id and item not in merged:
                    merged.append(item)
            merged = merged[:2]
            lines[i] = f"{prefix}{needle} {', '.join(merged)}"
            return
        raise ValueError(f"missing `{key}:` in {path}")

    replace_meta("LastStepID", step_id)
    replace_meta("Last InfoGain", info_gain)
    if approach_tag:
        replace_meta("LastApproachTag", approach_tag)
    if failure_reason:
        replace_meta("LastFailureReason", failure_reason)
    update_do_not_repeat("Do-not-repeat (next 2 runs)")

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Append a single artifact entry and update agent brief.")
    parser.add_argument("--step-id", required=True, help="StepID like Q39.S27-foo")
    parser.add_argument("--type", required=True, choices=sorted(_ALLOWED_TYPES))
    parser.add_argument("--lean-target", required=True, help="Target Lean file")
    parser.add_argument("--info-gain", required=True, choices=["0", "1", "2"])
    parser.add_argument("--approach-tag", default="", help="Optional approach tag")
    parser.add_argument("--failure-reason", default="", help="Optional failure reason")
    parser.add_argument("--notes", default="", help="Optional notes")
    parser.add_argument("--commit", default="", help="Commit hash (defaults to HEAD for done log)")
    parser.add_argument("--planned", action="store_true", help="Write to planned log with PENDING commit")
    parser.add_argument("--artifacts", default="docs/artifacts.tsv", help="Path to done artifacts log")
    parser.add_argument("--planned-log", default="docs/planned.tsv", help="Path to planned log")
    parser.add_argument("--agent-brief", default="docs/agent_brief.md", help="Path to agent brief")
    args = parser.parse_args()

    step_id = _parse_step_id(args.step_id)
    art_type = args.type
    lean_target = args.lean_target.strip()
    info_gain = args.info_gain.strip()
    notes = args.notes.strip()
    if args.planned:
        if args.commit.strip() and args.commit.strip() != "PENDING":
            print("error: planned log only accepts Commit=PENDING", file=sys.stderr)
            return 2
        commit = _parse_commit("PENDING", allow_pending=True, default_to_head=False)
        artifacts_path = Path(args.planned_log)
    else:
        commit = _parse_commit(args.commit, allow_pending=False, default_to_head=True)
        artifacts_path = Path(args.artifacts)

    if not lean_target:
        print("error: empty --lean-target", file=sys.stderr)
        return 2

    headers, rows = _load_artifacts(artifacts_path)
    if headers != ["StepID", "Type", "LeanTarget", "Commit", "Notes"]:
        print(f"error: unexpected header in {artifacts_path}: {headers}", file=sys.stderr)
        return 2

    if any((row.get("StepID") or "").strip() == step_id for row in rows):
        print(f"error: StepID already present in {artifacts_path}: {step_id}", file=sys.stderr)
        return 2

    rows.append(
        {
            "StepID": step_id,
            "Type": art_type,
            "LeanTarget": lean_target,
            "Commit": commit,
            "Notes": notes,
        }
    )
    _write_artifacts(artifacts_path, headers, rows)

    if not args.planned:
        _update_agent_brief(
            Path(args.agent_brief),
            step_id=step_id,
            info_gain=info_gain,
            approach_tag=args.approach_tag.strip() or None,
            failure_reason=args.failure_reason.strip() or None,
        )

    print(f"OK: registered {step_id} ({art_type})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
