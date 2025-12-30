#!/usr/bin/env bash
set -u

status=0

check_required() {
  local name="$1"
  if command -v "$name" >/dev/null 2>&1; then
    echo "OK: $name"
  else
    echo "MISSING: $name"
    status=1
  fi
}

check_optional() {
  local name="$1"
  if command -v "$name" >/dev/null 2>&1; then
    echo "OK: $name"
  else
    echo "WARN: missing optional $name"
  fi
}

check_required python3
check_required git
check_optional rg
check_optional lake
check_optional pdftotext
check_optional codex

if [ -f formal/lean-toolchain ]; then
  echo "OK: formal/lean-toolchain present"
else
  echo "WARN: formal/lean-toolchain missing"
fi

if [ -f formal/lakefile.lean ]; then
  echo "OK: formal/lakefile.lean present"
else
  echo "WARN: formal/lakefile.lean missing"
fi

exit "$status"
