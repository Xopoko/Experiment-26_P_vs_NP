#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKER_PROMPT_FILE="${WORKER_PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
SUPERVISOR_PROMPT_FILE="${SUPERVISOR_PROMPT_FILE:-$ROOT/scripts/supervisor_prompt.txt}"

LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.duo.log}"
MAX_ROUNDS="${MAX_ROUNDS:-}"
PAUSE_SECONDS="${PAUSE_SECONDS:-}"

if [[ ! -f "$WORKER_PROMPT_FILE" ]]; then
  echo "error: worker prompt file not found: $WORKER_PROMPT_FILE" >&2
  exit 2
fi
if [[ ! -f "$SUPERVISOR_PROMPT_FILE" ]]; then
  echo "error: supervisor prompt file not found: $SUPERVISOR_PROMPT_FILE" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
ln -sf "$(basename "$LOG_FILE")" "$LOG_DIR/latest_duo.log"

for arg in "$@"; do
  case "$arg" in
    --infinite|infinite)
      echo "error: do not pass --infinite to run_duo.sh (it already loops forever)" >&2
      exit 2
      ;;
  esac
done

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  echo "mode: duo"
  echo "worker_prompt: $WORKER_PROMPT_FILE"
  echo "supervisor_prompt: $SUPERVISOR_PROMPT_FILE"
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
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$WORKER_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  {
    echo
    echo "==== SUPERVISOR round=$round $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$SUPERVISOR_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  if [[ -n "$PAUSE_SECONDS" ]]; then
    sleep "$PAUSE_SECONDS"
  fi
done
