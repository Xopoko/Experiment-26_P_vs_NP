#!/usr/bin/env python3
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
FORMAL_DIR = ROOT / "formal"
CHECK_FILE = FORMAL_DIR / "Checks" / "AxiomsCheck.lean"


def main() -> int:
    if not CHECK_FILE.exists():
        print(f"FAILED: missing {CHECK_FILE}", file=sys.stderr)
        return 2

    rel_check = CHECK_FILE.relative_to(FORMAL_DIR)
    proc = subprocess.run(
        ["lake", "env", "lean", str(rel_check)],
        cwd=FORMAL_DIR,
        capture_output=True,
        text=True,
        env=os.environ.copy(),
    )

    output = (proc.stdout or "") + (proc.stderr or "")
    if proc.returncode != 0:
        print("FAILED: axioms check failed to run", file=sys.stderr)
        if output:
            print(output, file=sys.stderr)
        return proc.returncode or 1

    if "sorryAx" in output or "ASSUMPTION_" in output:
        print("FAILED: axioms check found forbidden axioms (sorryAx/ASSUMPTION_)", file=sys.stderr)
        print(output, file=sys.stderr)
        return 1

    print(f"OK: axioms check passed ({rel_check})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
