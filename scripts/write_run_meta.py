#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _git_changed_files() -> list[str]:
    if not shutil.which("git"):
        return []
    try:
        subprocess.run(["git", "rev-parse", "--is-inside-work-tree"], check=True, stdout=subprocess.DEVNULL)
    except Exception:
        return []

    def _run(cmd: list[str]) -> list[str]:
        res = subprocess.run(cmd, check=False, capture_output=True, text=True)
        if res.returncode != 0:
            return []
        return [line.strip() for line in res.stdout.splitlines() if line.strip()]

    files = set()
    files.update(_run(["git", "diff", "--name-only"]))
    files.update(_run(["git", "diff", "--name-only", "--cached"]))
    files.update(_run(["git", "ls-files", "--others", "--exclude-standard"]))
    return sorted(files)


def _extract_backticked_meta(lines: list[str], key: str) -> str | None:
    needle = f"`{key}:`"
    for line in lines:
        if needle not in line:
            continue
        return line.split(needle, 1)[1].strip()
    return None


def _parse_int(value: str | None) -> int | None:
    if value is None:
        return None
    raw = value.strip().split()[0] if value.strip() else ""
    if not raw.lstrip("-").isdigit():
        return None
    return int(raw)


def _agent_brief_meta(path: Path) -> tuple[int | None, str | None]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None, None
    info_gain = _parse_int(_extract_backticked_meta(lines, "Last InfoGain"))
    failure_reason = _extract_backticked_meta(lines, "LastFailureReason")
    return info_gain, failure_reason.strip() if failure_reason else None


def _compute_entropy(contract_path: Path) -> dict[str, object] | None:
    cmd = [
        sys.executable,
        "scripts/stopper_advice.py",
        "--contract",
        str(contract_path),
        "--mode",
        "post",
        "--json",
    ]
    res = subprocess.run(cmd, check=False, capture_output=True, text=True)
    if res.returncode not in {0, 42}:
        print(
            f"WARN: stopper_advice failed (exit {res.returncode})",
            file=sys.stderr,
        )
        return None
    stdout = (res.stdout or "").strip()
    if not stdout:
        print("WARN: stopper_advice returned empty output", file=sys.stderr)
        return None
    try:
        data = json.loads(stdout)
    except json.JSONDecodeError as exc:
        print(f"WARN: stopper_advice JSON parse error: {exc}", file=sys.stderr)
        return None
    return data if isinstance(data, dict) else None


def main() -> int:
    parser = argparse.ArgumentParser(description="Write a structured run meta JSON.")
    parser.add_argument("--outcome", required=True, choices=["DONE", "BLOCKED", "FAIL"])
    parser.add_argument("--selected-item", required=True)
    parser.add_argument("--step-id", required=True)
    parser.add_argument("--verify-cmd", default="", help="Verification command used")
    parser.add_argument("--verify-exit-code", type=int, default=None)
    parser.add_argument("--notes", default="")
    parser.add_argument("--run-id", default=os.environ.get("RUN_ID"))
    parser.add_argument("--out", default=os.environ.get("RUN_META_FILE"))
    parser.add_argument(
        "--no-scan-git",
        action="store_true",
        help="Skip git scan for touched files",
    )
    args = parser.parse_args()

    if not args.run_id or not args.out:
        raise SystemExit("missing RUN_ID or RUN_META_FILE (or --run-id/--out)")

    touched = [] if args.no_scan_git else _git_changed_files()
    info_gain, failure_reason = _agent_brief_meta(Path("docs/agent_brief.md"))

    entropy = None
    contract_file = os.environ.get("CONTRACT_FILE")
    if contract_file:
        contract_path = Path(contract_file)
        if contract_path.exists():
            entropy = _compute_entropy(contract_path)

    payload = {
        "schema_version": 1,
        "run_id": args.run_id,
        "ended_at": _utc_now(),
        "selected_item": args.selected_item,
        "step_id": args.step_id,
        "outcome": args.outcome,
        "touched_files": touched,
        "verify_cmd": args.verify_cmd.strip(),
        "verify_exit_code": args.verify_exit_code,
        "info_gain": info_gain,
        "last_failure_reason": failure_reason,
        "notes": args.notes.strip(),
        "entropy": entropy,
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"OK: wrote run meta to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
