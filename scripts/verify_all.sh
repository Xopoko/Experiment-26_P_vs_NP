#!/usr/bin/env bash
set -euo pipefail

verify_args=()
if [ "${SKIP_RESOURCE_CHECKS:-}" = "1" ] || [ ! -d resources/downloads ]; then
  verify_args+=(--skip-resource-checks)
fi
python3 scripts/verify_notebook.py "${verify_args[@]}"

if [ "${REQUIRE_CONTRACT:-}" = "1" ] || [ -n "${CONTRACT_FILE:-}" ]; then
  python3 scripts/verify_run_contract.py
fi

if [ -d formal ] && [ -f formal/lakefile.lean ]; then
  if [ "${FORMAL_SKIP:-}" = "1" ] && [ "${ALLOW_FORMAL_SKIP:-}" != "1" ]; then
    echo "FAIL: FORMAL_SKIP=1 requires ALLOW_FORMAL_SKIP=1" >&2
    exit 1
  fi
  if [ "${FORMAL_SKIP:-}" = "1" ]; then
    echo "SKIP: FORMAL_SKIP=1"
    exit 0
  fi
  set_default() {
    local name="$1"
    local val="$2"
    if [ -z "${!name-}" ]; then
      printf -v "$name" '%s' "$val"
    fi
  }

  RUN_MODE="${RUN_MODE:-}"
  case "$RUN_MODE" in
    docs)
      set_default REQUIRE_LEAN 0
      set_default BUILD_NOTES 0
      set_default BUILD_WIP 0
      set_default CHECK_AXIOMS 0
      ;;
    wip)
      set_default REQUIRE_LEAN 1
      set_default BUILD_NOTES 0
      set_default BUILD_WIP 1
      set_default CHECK_AXIOMS 0
      ;;
    core|"")
      set_default REQUIRE_LEAN 1
      set_default BUILD_NOTES 0
      set_default BUILD_WIP 0
      set_default CHECK_AXIOMS 1
      ;;
    *)
      echo "FAIL: unknown RUN_MODE '$RUN_MODE' (expected docs|wip|core)" >&2
      exit 2
      ;;
  esac

  changed=""
  if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    changed="$(
      {
        git diff --name-only
        git diff --name-only --cached
        git ls-files --others --exclude-standard
      } 2>/dev/null | sort -u
    )"
    if printf '%s\n' "$changed" | grep -q '^formal/WIP/'; then
      BUILD_WIP=1
    fi
    if printf '%s\n' "$changed" | grep -q '^formal/Notes/'; then
      BUILD_NOTES=1
    fi
  fi
  if [ "${REQUIRE_LEAN:-}" = "0" ] && [ -n "$changed" ]; then
    if printf '%s\n' "$changed" | grep -q '^formal/'; then
      if [ "${ALLOW_REQUIRE_LEAN_SKIP:-}" != "1" ]; then
        echo "FAIL: REQUIRE_LEAN=0 for formal changes requires ALLOW_REQUIRE_LEAN_SKIP=1" >&2
        exit 1
      fi
    fi
  fi

  if command -v lake >/dev/null 2>&1; then
    if [ "${LEAN_FORCE_REBUILD:-1}" = "1" ]; then
      echo "INFO: LEAN_FORCE_REBUILD=1 (running lake clean PvNP)"
      (cd formal && lake clean PvNP)
    fi
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
    wip_verified_dir="formal/WIP/Verified"
    if [ -d "$wip_verified_dir" ]; then
      if scan_for_pattern "(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)" "$wip_verified_dir"; then
        echo "FAIL: found sorry/admit in $wip_verified_dir" >&2
        exit 1
      fi
      if scan_for_pattern "(^|[^[:alnum:]_])axiom([^[:alnum:]_]|$)" "$wip_verified_dir"; then
        echo "FAIL: found axiom in $wip_verified_dir" >&2
        exit 1
      fi
    fi

    scan_for_placeholders() {
      local dir="$1"
      if scan_for_pattern "^[[:space:]]*(def|theorem|lemma)[[:space:]]+[^[:space:]]+[[:space:]]*:[[:space:]]*Prop[[:space:]]*:=[[:space:]]*True([[:space:]]|$)" "$dir"; then
        echo "FAIL: found placeholder Prop := True in $dir (move notes to formal/Notes or docs)" >&2
        exit 1
      fi
      if scan_for_pattern "^[[:space:]]*@\\[[^]]+\\][[:space:]]*(def|theorem|lemma)[[:space:]]+[^[:space:]]+[[:space:]]*:[[:space:]]*Prop[[:space:]]*:=[[:space:]]*True([[:space:]]|$)" "$dir"; then
        echo "FAIL: found placeholder Prop := True in $dir (move notes to formal/Notes or docs)" >&2
        exit 1
      fi
      if scan_for_pattern "^[[:space:]]*(theorem|lemma)[[:space:]]+[^[:space:]]+[[:space:]]*:[[:space:]]*True[[:space:]]*:=[[:space:]]*by([[:space:]]|$)" "$dir"; then
        echo "FAIL: found placeholder theorem : True := by in $dir (move notes to formal/Notes or docs)" >&2
        exit 1
      fi
      if scan_for_pattern "^[[:space:]]*@\\[[^]]+\\][[:space:]]*(theorem|lemma)[[:space:]]+[^[:space:]]+[[:space:]]*:[[:space:]]*True[[:space:]]*:=[[:space:]]*by([[:space:]]|$)" "$dir"; then
        echo "FAIL: found placeholder theorem : True := by in $dir (move notes to formal/Notes or docs)" >&2
        exit 1
      fi
    }

    if [ -d "$core_dir" ]; then
      scan_for_placeholders "$core_dir"
    fi
    if [ -d "$wip_verified_dir" ]; then
      scan_for_placeholders "$wip_verified_dir"
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
