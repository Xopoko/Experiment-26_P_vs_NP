#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKER_PROMPT_FILE="${WORKER_PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
SUPERVISOR_PROMPT_FILE="${SUPERVISOR_PROMPT_FILE:-$ROOT/scripts/supervisor_prompt.txt}"

LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.duo.log}"

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

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  echo "mode: duo"
  echo "worker_prompt: $WORKER_PROMPT_FILE"
  echo "supervisor_prompt: $SUPERVISOR_PROMPT_FILE"
} >>"$LOG_FILE"

while true; do
  {
    echo
    echo "==== WORKER $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$WORKER_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"

  {
    echo
    echo "==== SUPERVISOR $(date -Is) ===="
  } | tee -a "$LOG_FILE"
  "$ROOT/agent/codex-run.sh" -C "$ROOT" --file "$SUPERVISOR_PROMPT_FILE" "$@" 2>&1 | tee -a "$LOG_FILE"
done
