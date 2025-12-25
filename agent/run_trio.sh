#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKER_PROMPT_FILE="${WORKER_PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
SKEPTIC_PROMPT_FILE="${SKEPTIC_PROMPT_FILE:-$ROOT/scripts/skeptic_prompt.txt}"
SUPERVISOR_PROMPT_FILE="${SUPERVISOR_PROMPT_FILE:-$ROOT/scripts/supervisor_prompt.txt}"

LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.trio.log}"
LOCK_FILE="${LOCK_FILE:-$LOG_DIR/.agent.lock}"
MAX_ROUNDS="${MAX_ROUNDS:-}"
PAUSE_SECONDS="${PAUSE_SECONDS:-}"
REQUIRE_CLEAN="${REQUIRE_CLEAN:-}"

if [[ ! -f "$WORKER_PROMPT_FILE" ]]; then
  echo "error: worker prompt file not found: $WORKER_PROMPT_FILE" >&2
  exit 2
fi
if [[ ! -f "$SKEPTIC_PROMPT_FILE" ]]; then
  echo "error: skeptic prompt file not found: $SKEPTIC_PROMPT_FILE" >&2
  exit 2
fi
if [[ ! -f "$SUPERVISOR_PROMPT_FILE" ]]; then
  echo "error: supervisor prompt file not found: $SUPERVISOR_PROMPT_FILE" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
ln -sf "$(basename "$LOG_FILE")" "$LOG_DIR/latest_trio.log"

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

for arg in "$@"; do
  case "$arg" in
    --infinite|infinite)
      echo "error: do not pass --infinite to run_trio.sh (it already loops forever)" >&2
      exit 2
      ;;
  esac
done

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  echo "mode: trio"
  echo "worker_prompt: $WORKER_PROMPT_FILE"
  echo "skeptic_prompt: $SKEPTIC_PROMPT_FILE"
  echo "supervisor_prompt: $SUPERVISOR_PROMPT_FILE"
  echo "require_clean: ${REQUIRE_CLEAN:-0}"
  echo "lock: $LOCK_FILE"
  if [[ -n "$MAX_ROUNDS" ]]; then
    echo "max_rounds: $MAX_ROUNDS"
  fi
  if [[ -n "$PAUSE_SECONDS" ]]; then
    echo "pause_seconds: $PAUSE_SECONDS"
  fi
} >>"$LOG_FILE"

round=0
while true; do
  round=$((round + 1))
  if [[ -n "$MAX_ROUNDS" ]] && [[ "$round" -gt "$MAX_ROUNDS" ]]; then
    echo "stopping: reached MAX_ROUNDS=$MAX_ROUNDS" | tee -a "$LOG_FILE"
    exit 0
  fi

  {
    echo
    echo "==== WORKER round=$round $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  if is_truthy "$REQUIRE_CLEAN"; then
    require_clean_worktree
  fi
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$WORKER_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  {
    echo
    echo "==== SKEPTIC round=$round $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  if is_truthy "$REQUIRE_CLEAN"; then
    require_clean_worktree
  fi
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$SKEPTIC_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  {
    echo
    echo "==== SUPERVISOR round=$round $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  if is_truthy "$REQUIRE_CLEAN"; then
    require_clean_worktree
  fi
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$SUPERVISOR_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  if [[ -n "$PAUSE_SECONDS" ]]; then
    sleep "$PAUSE_SECONDS"
  fi
done

