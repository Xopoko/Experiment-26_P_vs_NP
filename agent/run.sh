#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROMPT_FILE="${PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)_pid$$}"
LOG_FILE="${LOG_FILE:-$LOG_DIR/$RUN_ID.log}"

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "error: prompt file not found: $PROMPT_FILE" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
ln -sf "$(basename "$LOG_FILE")" "$LOG_DIR/latest.log"

cmd=("$ROOT/agent/codex-run.sh" --infinite -C "$ROOT" --file "$PROMPT_FILE" "$@")

{
  echo "---- $(date -Is) ----"
  echo "run_id: $RUN_ID"
  printf 'cmd:'
  printf ' %q' "${cmd[@]}"
  echo
} >>"$LOG_FILE"

"${cmd[@]}" 2>&1 | tee -a "$LOG_FILE"
