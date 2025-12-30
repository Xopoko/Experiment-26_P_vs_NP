#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROMPT_FILE="${PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.log}"
CONTRACT_FILE="${CONTRACT_FILE:-$LOG_DIR/$RUN_ID.contract.json}"
RUN_META_FILE="${RUN_META_FILE:-$LOG_DIR/$RUN_ID.meta.json}"
LOCK_FILE="${LOCK_FILE:-$LOG_DIR/.agent.lock}"
REQUIRE_CLEAN="${REQUIRE_CLEAN:-}"
RUN_MODE="${RUN_MODE:-core}"
REQUIRE_CONTRACT="${REQUIRE_CONTRACT:-1}"

export RUN_MODE
export RUN_ID LOG_FILE CONTRACT_FILE RUN_META_FILE REQUIRE_CONTRACT

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "error: prompt file not found: $PROMPT_FILE" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
ln -sf "$(basename "$LOG_FILE")" "$LOG_DIR/latest.log"

is_truthy() {
  case "${1:-}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    *) return 1 ;;
  esac
}

require_clean_worktree() {
  if ! command -v git >/dev/null 2>&1; then
    return 0
  fi
  if ! git -C "$ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    return 0
  fi
  if [[ -n "$(git -C "$ROOT" status --porcelain)" ]]; then
    echo "error: git working tree is not clean (set REQUIRE_CLEAN=0 to bypass)" >&2
    git -C "$ROOT" status --porcelain >&2 || true
    exit 4
  fi
}

acquire_lock() {
  mkdir -p "$LOG_DIR"

  if command -v flock >/dev/null 2>&1; then
    local lock_fd
    exec {lock_fd}>"$LOCK_FILE"
    if ! flock -n "$lock_fd"; then
      echo "error: another agent runner is active (lock: $LOCK_FILE)" >&2
      exit 3
    fi
    printf '%s\n' "$$" >&"$lock_fd" || true
    return 0
  fi

  local lock_dir="${LOCK_FILE}.d"
  if ! mkdir "$lock_dir" 2>/dev/null; then
    echo "error: another agent runner is active (lock dir: $lock_dir)" >&2
    exit 3
  fi
  echo "$$" >"$lock_dir/pid" 2>/dev/null || true
  trap 'rm -rf "$lock_dir" >/dev/null 2>&1 || true' EXIT INT TERM
}

acquire_lock
if is_truthy "$REQUIRE_CLEAN"; then
  require_clean_worktree
fi

cmd=("$ROOT/agent/codex-run.sh" --infinite -C "$ROOT" --file "$PROMPT_FILE" "$@")

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  echo "require_clean: ${REQUIRE_CLEAN:-0}"
  echo "run_mode: $RUN_MODE"
  echo "contract_file: $CONTRACT_FILE"
  echo "run_meta_file: $RUN_META_FILE"
  echo "lock: $LOCK_FILE"
  printf 'cmd:'
  printf ' %q' "${cmd[@]}"
  echo
} >>"$LOG_FILE"

"${cmd[@]}" 2>&1 | tee -a "$LOG_FILE"
