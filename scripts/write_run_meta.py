#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
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
        "notes": args.notes.strip(),
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"OK: wrote run meta to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
