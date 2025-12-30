#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import fnmatch
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")
_ALLOWED_TYPES = {"Proof", "Counterexample", "Exact citation", "Toy", "Reduction", "Barrier"}

_DEFAULT_ALLOW_PATTERNS = [
    "agent/logs/*",
    "docs/q*_s*.md",
]


def _git_changed_files() -> list[str]:
    if not shutil.which("git"):
        return []
    try:
        subprocess.run(
            ["git", "rev-parse", "--is-inside-work-tree"],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
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


def _git_root() -> Path | None:
    if not shutil.which("git"):
        return None
    try:
        res = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception:
        return None
    root = res.stdout.strip()
    return Path(root) if root else None


def _normalize_paths(paths: list[str]) -> list[str]:
    root = _git_root()
    normalized: list[str] = []
    for raw in paths:
        p = Path(raw)
        if p.is_absolute() and root:
            try:
                p = p.relative_to(root)
            except ValueError:
                pass
        normalized.append(str(p))
    return normalized

def _load_contract(path: Path) -> dict[str, object]:
    raw = path.read_text(encoding="utf-8")
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise AssertionError("contract payload must be a JSON object")
    return data


def _require_field(data: dict[str, object], key: str) -> object:
    if key not in data:
        raise AssertionError(f"contract missing field: {key}")
    return data[key]


def _parse_step_id(value: object) -> str:
    if not isinstance(value, str) or not value.strip():
        raise AssertionError("contract step_id must be a non-empty string")
    token = value.strip()
    if not _STEP_ID_RE.match(token):
        raise AssertionError(f"contract step_id invalid: {token!r}")
    return token


def _load_artifact_row(path: Path, *, step_id: str) -> dict[str, str] | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        for row in reader:
            if (row.get("StepID") or "").strip() == step_id:
                return {k: (v or "").strip() for k, v in row.items()}
    return None


def _matches_patterns(path: str, patterns: list[str]) -> bool:
    return any(fnmatch.fnmatch(path, pat) for pat in patterns)


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify a run contract against git state + logs.")
    parser.add_argument(
        "--contract",
        default=os.environ.get("CONTRACT_FILE"),
        help="Path to contract JSON (env CONTRACT_FILE)",
    )
    parser.add_argument(
        "--require",
        action="store_true",
        help="Fail if contract is missing",
    )
    parser.add_argument(
        "--allow",
        action="append",
        default=[],
        help="Extra allowlist glob pattern (repeatable)",
    )
    args = parser.parse_args()

    contract_path = args.contract
    require_contract = args.require or os.environ.get("REQUIRE_CONTRACT") == "1"

    if not contract_path:
        if require_contract:
            print("FAIL: CONTRACT_FILE not set", file=sys.stderr)
            return 2
        print("SKIP: contract check (no CONTRACT_FILE)")
        return 0

    path = Path(contract_path)
    if not path.exists():
        if require_contract:
            print(f"FAIL: contract file missing: {path}", file=sys.stderr)
            return 2
        print(f"SKIP: contract check (missing {path})")
        return 0

    data = _load_contract(path)
    step_id = _parse_step_id(_require_field(data, "step_id"))
    artifact_type = _require_field(data, "artifact_type")
    if artifact_type not in _ALLOWED_TYPES:
        raise AssertionError(f"contract artifact_type invalid: {artifact_type!r}")
    lean_target = _require_field(data, "lean_target")
    if not isinstance(lean_target, str) or not lean_target.strip():
        raise AssertionError("contract lean_target must be a non-empty string")

    files_to_touch = _require_field(data, "files_to_touch")
    if not isinstance(files_to_touch, list) or not files_to_touch:
        raise AssertionError("contract files_to_touch must be a non-empty list")
    files_to_touch = _normalize_paths([str(p) for p in files_to_touch if str(p).strip()])

    allow_patterns = _DEFAULT_ALLOW_PATTERNS + args.allow
    allow_patterns.append(str(path))
    meta_path = os.environ.get("RUN_META_FILE")
    if meta_path:
        allow_patterns.append(meta_path)

    changed = _git_changed_files()
    if changed:
        allowed = set(files_to_touch)
        violations = [
            p for p in changed if p not in allowed and not _matches_patterns(p, allow_patterns)
        ]
        if violations:
            print("FAIL: contract file-touch violations:", file=sys.stderr)
            for v in violations:
                print(f"- {v}", file=sys.stderr)
            return 1
    else:
        print("WARN: git change detection skipped (no git or clean tree)")

    planned = bool(data.get("planned", False))
    artifacts_path = Path("docs/artifacts.tsv")
    planned_path = Path("docs/planned.tsv")

    row_done = _load_artifact_row(artifacts_path, step_id=step_id)
    row_plan = _load_artifact_row(planned_path, step_id=step_id)

    if planned:
        if row_plan is None:
            print(f"FAIL: StepID {step_id} not found in {planned_path}", file=sys.stderr)
            return 1
        if row_done is not None:
            print(f"FAIL: StepID {step_id} present in {artifacts_path} but contract says planned", file=sys.stderr)
            return 1
        row = row_plan
    else:
        if row_done is None:
            print(f"FAIL: StepID {step_id} not found in {artifacts_path}", file=sys.stderr)
            return 1
        if row_plan is not None:
            print(f"FAIL: StepID {step_id} present in {planned_path} but contract says done", file=sys.stderr)
            return 1
        row = row_done

    if row is None:
        print("FAIL: missing artifact row for contract StepID", file=sys.stderr)
        return 1

    row_type = row.get("Type", "")
    if row_type != artifact_type:
        print(
            f"FAIL: artifact Type mismatch (contract {artifact_type}, log {row_type})",
            file=sys.stderr,
        )
        return 1

    row_target = row.get("LeanTarget", "")
    if row_target != lean_target:
        print(
            f"FAIL: LeanTarget mismatch (contract {lean_target}, log {row_target})",
            file=sys.stderr,
        )
        return 1

    print(f"OK: verified run contract {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
