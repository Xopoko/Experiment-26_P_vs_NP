#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QUESTION_PROMPT_FILE="${QUESTION_PROMPT_FILE:-$ROOT/scripts/question_prompt.txt}"
WORKER_PROMPT_FILE="${WORKER_PROMPT_FILE:-$ROOT/scripts/worker_prompt.txt}"
SKEPTIC_PROMPT_FILE="${SKEPTIC_PROMPT_FILE:-$ROOT/scripts/skeptic_prompt.txt}"

LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.flow.log}"
LOCK_FILE="${LOCK_FILE:-$LOG_DIR/.agent.lock}"
MAX_ROUNDS="${MAX_ROUNDS:-}"
PAUSE_SECONDS="${PAUSE_SECONDS:-}"
REQUIRE_CLEAN="${REQUIRE_CLEAN:-}"
SKEPTIC_EVERY="${SKEPTIC_EVERY:-}"

if [[ ! -f "$QUESTION_PROMPT_FILE" ]]; then
  echo "error: question prompt file not found: $QUESTION_PROMPT_FILE" >&2
  exit 2
fi
if [[ ! -f "$WORKER_PROMPT_FILE" ]]; then
  echo "error: worker prompt file not found: $WORKER_PROMPT_FILE" >&2
  exit 2
fi
if [[ -n "$SKEPTIC_EVERY" ]] && [[ ! -f "$SKEPTIC_PROMPT_FILE" ]]; then
  echo "error: skeptic prompt file not found: $SKEPTIC_PROMPT_FILE" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
ln -sf "$(basename "$LOG_FILE")" "$LOG_DIR/latest_flow.log"

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
      echo "error: do not pass --infinite to run_flow.sh (it already loops forever)" >&2
      exit 2
      ;;
  esac
done

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  echo "mode: flow"
  echo "question_prompt: $QUESTION_PROMPT_FILE"
  echo "worker_prompt: $WORKER_PROMPT_FILE"
  echo "skeptic_prompt: $SKEPTIC_PROMPT_FILE"
  echo "require_clean: ${REQUIRE_CLEAN:-0}"
  echo "lock: $LOCK_FILE"
  if [[ -n "$MAX_ROUNDS" ]]; then
    echo "max_rounds: $MAX_ROUNDS"
  fi
  if [[ -n "$PAUSE_SECONDS" ]]; then
    echo "pause_seconds: $PAUSE_SECONDS"
  fi
  if [[ -n "$SKEPTIC_EVERY" ]]; then
    echo "skeptic_every: $SKEPTIC_EVERY"
  else
    echo "skeptic_every: 0"
  fi
} >>"$LOG_FILE"

round=0
while true; do
  round=$((round + 1))
  if [[ -n "$MAX_ROUNDS" ]] && [[ "$round" -gt "$MAX_ROUNDS" ]]; then
    echo "stopping: reached MAX_ROUNDS=$MAX_ROUNDS" | tee -a "$LOG_FILE"
    exit 0
  fi

question_out="$LOG_DIR/$RUN_ID.round${round}.question.txt"
combined_prompt="$LOG_DIR/$RUN_ID.round${round}.worker_combined_prompt.txt"

  {
    echo
    echo "==== QUESTION_SETTER round=$round $(date -Is) ===="
    echo "question_out: $question_out"
  } | tee -a "$LOG_FILE"
  if is_truthy "$REQUIRE_CLEAN"; then
    require_clean_worktree
  fi
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$QUESTION_PROMPT_FILE" --output-last-message "$question_out" "$@" 2>&1 | tee -a "$LOG_FILE"

  # Build a combined prompt for WORKER that includes the Question Set content.
  {
    cat "$WORKER_PROMPT_FILE"
    echo
    echo
    echo "Question Set (from QUESTION_SETTER):"
    echo
    if [[ -s "$question_out" ]]; then
      cat "$question_out"
    else
      echo "(missing question_out; proceed by selecting one micro-step yourself)"
    fi
  } >"$combined_prompt"

  {
    echo
    echo "==== WORKER round=$round $(date -Is) ===="
    echo "worker_prompt_combined: $combined_prompt"
  } | tee -a "$LOG_FILE"
  if is_truthy "$REQUIRE_CLEAN"; then
    require_clean_worktree
  fi
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$combined_prompt" "$@" 2>&1 | tee -a "$LOG_FILE"

  if [[ -n "$SKEPTIC_EVERY" ]] && [[ "$SKEPTIC_EVERY" =~ ^[0-9]+$ ]] && ((SKEPTIC_EVERY > 0)) && ((round % SKEPTIC_EVERY == 0)); then
    {
      echo
      echo "==== SKEPTIC round=$round $(date -Is) ===="
    } | tee -a "$LOG_FILE"
    if is_truthy "$REQUIRE_CLEAN"; then
      require_clean_worktree
    fi
    "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$SKEPTIC_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"
  fi

  if [[ -n "$PAUSE_SECONDS" ]]; then
    sleep "$PAUSE_SECONDS"
  fi
done

