#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROMPT_FILE="${PROMPT_FILE:-$ROOT/scripts/agent_prompt.txt}"
LOG_FILE="${LOG_FILE:-$ROOT/log.txt}"

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "error: prompt file not found: $PROMPT_FILE" >&2
  exit 2
fi

cmd=("$ROOT/agent/codex-run.sh" --infinite -C "$ROOT" --file "$PROMPT_FILE" "$@")

{
  echo "---- $(date -Is) ----"
  printf 'cmd:'
  printf ' %q' "${cmd[@]}"
  echo
} >>"$LOG_FILE"

"${cmd[@]}" 2>&1 | tee -a "$LOG_FILE"
