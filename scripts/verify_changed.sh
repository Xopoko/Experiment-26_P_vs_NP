#!/usr/bin/env bash
set -euo pipefail

if ! command -v git >/dev/null 2>&1; then
  echo "INFO: git not found; running default verify"
  exec scripts/verify_all.sh
fi

if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "INFO: not inside git repo; running default verify"
  exec scripts/verify_all.sh
fi

changed="$(
  {
    git diff --name-only
    git diff --name-only --cached
    git ls-files --others --exclude-standard
  } 2>/dev/null | sort -u
)"

if [ -z "$changed" ]; then
  echo "INFO: no changes detected; running RUN_MODE=docs"
  RUN_MODE=docs exec scripts/verify_all.sh
fi

mode="docs"
if printf '%s\n' "$changed" | grep -q '^formal/PvNP/\|^formal/Checks/'; then
  mode="core"
elif printf '%s\n' "$changed" | grep -q '^formal/WIP/'; then
  mode="wip"
elif printf '%s\n' "$changed" | grep -q '^formal/Notes/\|^formal/Notes\.lean$'; then
  mode="core"
fi

if [ "$mode" = "docs" ]; then
  echo "INFO: docs-only changes detected; running RUN_MODE=docs"
else
  echo "INFO: formal changes detected; running RUN_MODE=$mode"
fi

RUN_MODE="$mode" exec scripts/verify_all.sh
