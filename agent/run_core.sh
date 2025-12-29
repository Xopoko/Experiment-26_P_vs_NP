#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export RUN_MODE="${RUN_MODE:-core}"
export LEAN_FORCE_REBUILD="${LEAN_FORCE_REBUILD:-1}"

exec "$ROOT/agent/run.sh" "$@"
