#!/usr/bin/env bash
set -euo pipefail

python3 scripts/verify_notebook.py

if [ -d formal ] && [ -f formal/lakefile.lean ]; then
  if [ "${FORMAL_SKIP:-}" = "1" ]; then
    echo "SKIP: FORMAL_SKIP=1"
    exit 0
  fi
  if command -v lake >/dev/null 2>&1; then
    (cd formal && lake build PvNP External Notes)
  else
    echo "SKIP: Lean build (lake not installed)"
  fi
fi
