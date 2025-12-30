#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path


_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")
_ALLOWED_TYPES = {"Proof", "Counterexample", "Exact citation", "Toy", "Reduction", "Barrier"}


def _required(value: str | None, *, name: str) -> str:
    if value is None or not value.strip():
        raise ValueError(f"missing required field: {name}")
    return value.strip()


def _parse_step_id(value: str) -> str:
    token = value.strip()
    if not _STEP_ID_RE.match(token):
        raise ValueError(f"invalid StepID {token!r} (expected Qxx.Sy.slug)")
    return token


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def main() -> int:
    parser = argparse.ArgumentParser(description="Write a machine-checkable run contract JSON.")
    parser.add_argument("--selected-item", required=True, help="Selected item id/title (e.g., Q43)")
    parser.add_argument("--step-id", required=True, help="StepID like Q43.S17-foo")
    parser.add_argument("--artifact-type", required=True, choices=sorted(_ALLOWED_TYPES))
    parser.add_argument("--lean-target", required=True, help="LeanTarget path or N/A")
    parser.add_argument(
        "--files-to-touch",
        action="append",
        default=[],
        help="File path to touch (repeatable)",
    )
    parser.add_argument("--oracle-cmd", default="", help="Oracle command (optional)")
    parser.add_argument("--stop-condition", default="", help="Stop condition (optional)")
    parser.add_argument("--planned", action="store_true", help="Write to planned log")
    parser.add_argument("--notes", default="", help="Optional notes")
    parser.add_argument("--run-id", default=os.environ.get("RUN_ID"), help="Run id (env RUN_ID)")
    parser.add_argument(
        "--out",
        default=os.environ.get("CONTRACT_FILE"),
        help="Output path (env CONTRACT_FILE)",
    )
    args = parser.parse_args()

    run_id = _required(args.run_id, name="run_id")
    out_path = Path(_required(args.out, name="out"))

    step_id = _parse_step_id(args.step_id)
    files_to_touch = [p.strip() for p in args.files_to_touch if p and p.strip()]
    if not files_to_touch:
        raise ValueError("files_to_touch cannot be empty")

    payload = {
        "schema_version": 1,
        "run_id": run_id,
        "created_at": _utc_now(),
        "selected_item": _required(args.selected_item, name="selected_item"),
        "step_id": step_id,
        "artifact_type": args.artifact_type,
        "lean_target": _required(args.lean_target, name="lean_target"),
        "files_to_touch": files_to_touch,
        "oracle_cmd": args.oracle_cmd.strip(),
        "stop_condition": args.stop_condition.strip(),
        "planned": bool(args.planned),
        "notes": args.notes.strip(),
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"OK: wrote run contract to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
