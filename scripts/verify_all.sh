#!/usr/bin/env bash
set -euo pipefail

python3 scripts/verify_notebook.py

if [ -d formal ] && [ -f formal/lakefile.lean ]; then
  if [ "${FORMAL_SKIP:-}" = "1" ]; then
    echo "SKIP: FORMAL_SKIP=1"
    exit 0
  fi
  REQUIRE_LEAN="${REQUIRE_LEAN:-1}"
  BUILD_NOTES="${BUILD_NOTES:-0}"
  BUILD_WIP="${BUILD_WIP:-0}"
  CHECK_AXIOMS="${CHECK_AXIOMS:-1}"

  if command -v lake >/dev/null 2>&1; then
    scan_for_pattern() {
      local pattern="$1"
      local dir="$2"
      local status=0
      if command -v rg >/dev/null 2>&1; then
        rg -n "$pattern" "$dir" || status=$?
      else
        grep -R -n -E "$pattern" "$dir" || status=$?
      fi
      if [ "$status" -eq 2 ]; then
        echo "FAIL: pattern scan error in $dir" >&2
        exit 1
      fi
      return "$status"
    }

    core_dir="formal/PvNP/Core"
    if [ -d "$core_dir" ]; then
      if scan_for_pattern "(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)" "$core_dir"; then
        echo "FAIL: found sorry/admit in $core_dir" >&2
        exit 1
      fi
      if scan_for_pattern "(^|[^[:alnum:]_])axiom([^[:alnum:]_]|$)" "$core_dir"; then
        echo "FAIL: found axiom in $core_dir" >&2
        exit 1
      fi
    fi

    (cd formal && lake build PvNP)
    if [ "$BUILD_NOTES" = "1" ]; then
      (cd formal && lake build Notes)
    fi
    if [ "$BUILD_WIP" = "1" ]; then
      (cd formal && lake build WIP)
    fi
    if [ "$CHECK_AXIOMS" = "1" ]; then
      python3 scripts/check_axioms.py
    fi
  else
    if [ "$REQUIRE_LEAN" = "1" ]; then
      echo "FAIL: Lean build required but lake is not installed (set REQUIRE_LEAN=0 to skip)" >&2
      exit 1
    fi
    echo "SKIP: Lean build (lake not installed; REQUIRE_LEAN=0)"
  fi
fi
