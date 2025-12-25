#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG_DIR="${LOG_DIR:-$ROOT/agent/logs}"
KEEP="${KEEP:-50}"
DAYS="${DAYS:-}"

usage() {
  cat <<'EOF'
Usage:
  ./agent/prune_logs.sh [--keep N] [--days D]

Defaults:
  KEEP=50 (keep newest 50 *.log files)

Environment:
  LOG_DIR=/path/to/logs
  KEEP=N
  DAYS=D

Notes:
  - Only regular files matching *.log are removed (symlinks like latest*.log are preserved).
  - --days runs before --keep.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --keep)
      KEEP="${2:-}"
      if [[ -z "$KEEP" ]]; then
        echo "error: --keep requires a number" >&2
        exit 2
      fi
      shift 2
      ;;
    --days)
      DAYS="${2:-}"
      if [[ -z "$DAYS" ]]; then
        echo "error: --days requires a number" >&2
        exit 2
      fi
      shift 2
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ ! -d "$LOG_DIR" ]]; then
  echo "OK: log dir does not exist: $LOG_DIR"
  exit 0
fi

if [[ -n "$DAYS" ]]; then
  find "$LOG_DIR" -maxdepth 1 -type f -name '*.log' -mtime "+$DAYS" -print -delete
fi

if [[ -n "$KEEP" ]]; then
  if ! [[ "$KEEP" =~ ^[0-9]+$ ]]; then
    echo "error: KEEP must be an integer, got: $KEEP" >&2
    exit 2
  fi

  mapfile -t files < <(
    find "$LOG_DIR" -maxdepth 1 -type f -name '*.log' -printf '%T@ %p\n' | sort -nr | awk '{print $2}'
  )

  if ((${#files[@]} > KEEP)); then
    for ((i = KEEP; i < ${#files[@]}; i++)); do
      rm -f "${files[i]}"
    done
  fi
fi

echo "OK: pruned logs in $LOG_DIR"
