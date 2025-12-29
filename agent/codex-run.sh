#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  ./codex-run.sh "Do X"
  ./codex-run.sh --file prompt.txt
  echo "Do X" | ./codex-run.sh

Options:
  -f, --file FILE              Read prompt from file
      --infinite               Re-run Codex forever (rotates session by default)
      --session-cycles N       In --infinite, start a new session every N runs (default: 10; 0 = never)
  -m, --model MODEL            Pass through to `codex exec --model`
  -s, --sandbox MODE           Pass through to `codex exec --sandbox`
  -a, --ask-for-approval MODE  Pass through to `codex exec --ask-for-approval`
  -p, --profile PROFILE        Pass through to `codex exec --profile`
  -C, --cd DIR                 Pass through to `codex exec -C`
      --json                   Pass through to `codex exec --json`
  -o, --output-last-message F  Pass through to `codex exec --output-last-message`
  -h, --help                   Show help

Notes:
  - If no prompt is provided, the prompt is read from stdin.
  - If not inside a git repo, `--skip-git-repo-check` is added automatically.
  - Runs Codex with `--dangerously-bypass-approvals-and-sandbox` by default.
  - In `--infinite` mode, stop with Ctrl+C.
EOF
}

prompt_file=""
infinite=false
session_cycles="${CODEX_SESSION_CYCLES:-10}"
model=""
sandbox=""
approval=""
profile=""
cd_dir=""
json=false
output_last_message=""
prompt_args=()
tty_mode="${CODEX_TTY:-auto}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --infinite|infinite)
      infinite=true
      shift
      ;;
    --session-cycles)
      session_cycles="${2:-}"
      if [[ -z "$session_cycles" ]]; then
        echo "error: --session-cycles requires a value" >&2
        exit 2
      fi
      if [[ ! "$session_cycles" =~ ^[0-9]+$ ]]; then
        echo "error: --session-cycles must be a non-negative integer" >&2
        exit 2
      fi
      shift 2
      ;;
    -f|--file)
      prompt_file="${2:-}"
      if [[ -z "$prompt_file" ]]; then
        echo "error: --file requires a path" >&2
        exit 2
      fi
      shift 2
      ;;
    -m|--model)
      model="${2:-}"
      if [[ -z "$model" ]]; then
        echo "error: --model requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    -s|--sandbox)
      sandbox="${2:-}"
      if [[ -z "$sandbox" ]]; then
        echo "error: --sandbox requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    -a|--ask-for-approval)
      approval="${2:-}"
      if [[ -z "$approval" ]]; then
        echo "error: --ask-for-approval requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    -p|--profile)
      profile="${2:-}"
      if [[ -z "$profile" ]]; then
        echo "error: --profile requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    -C|--cd)
      cd_dir="${2:-}"
      if [[ -z "$cd_dir" ]]; then
        echo "error: --cd requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    --json)
      json=true
      shift
      ;;
    -o|--output-last-message)
      output_last_message="${2:-}"
      if [[ -z "$output_last_message" ]]; then
        echo "error: --output-last-message requires a path" >&2
        exit 2
      fi
      shift 2
      ;;
    --)
      shift
      prompt_args+=("$@")
      break
      ;;
    *)
      prompt_args+=("$1")
      shift
      ;;
  esac
done

if [[ ! "$session_cycles" =~ ^[0-9]+$ ]]; then
  echo "error: session cycle count must be a non-negative integer" >&2
  exit 2
fi

if ! command -v codex >/dev/null 2>&1; then
  echo "error: 'codex' not found in PATH" >&2
  exit 127
fi

codex_cmd=(codex exec --dangerously-bypass-approvals-and-sandbox)

if [[ -n "$model" ]]; then
  codex_cmd+=(--model "$model")
fi
if [[ -n "$sandbox" ]]; then
  codex_cmd+=(--sandbox "$sandbox")
fi
if [[ -n "$approval" ]]; then
  codex_cmd+=(--ask-for-approval "$approval")
fi
if [[ -n "$profile" ]]; then
  codex_cmd+=(--profile "$profile")
fi
if [[ -n "$cd_dir" ]]; then
  codex_cmd+=(-C "$cd_dir")
fi
if [[ "$json" == "true" ]]; then
  codex_cmd+=(--json)
fi
if [[ -n "$output_last_message" ]]; then
  codex_cmd+=(--output-last-message "$output_last_message")
fi

inside_git_repo=false
if command -v git >/dev/null 2>&1; then
  if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    inside_git_repo=true
  fi
fi
if [[ "$inside_git_repo" != "true" ]]; then
  codex_cmd+=(--skip-git-repo-check)
fi

has_script=false
if command -v script >/dev/null 2>&1; then
  has_script=true
fi

should_use_tty() {
  case "${tty_mode}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    0|false|FALSE|no|NO|off|OFF) return 1 ;;
    *) [[ "$has_script" == "true" ]] ;;
  esac
}

cmd_to_string() {
  local out=""
  for arg in "$@"; do
    out+=$(printf '%q ' "$arg")
  done
  printf '%s' "${out% }"
}

extract_session_id_from_output() {
  local output_file="$1"
  local session_id=""

  if [[ "$json" == "true" ]]; then
    session_id="$(sed -E 's/\x1B\[[0-9;]*[[:alpha:]]//g' "$output_file" | tr -d '\r' | sed -nE 's/.*"thread_id":"([0-9a-fA-F-]{36})".*/\1/p' | head -n 1)"
  else
    session_id="$(sed -E 's/\x1B\[[0-9;]*[[:alpha:]]//g' "$output_file" | tr -d '\r' | sed -nE 's/^[[:space:]]*session id:[[:space:]]*([0-9a-fA-F-]{36}).*/\1/p' | head -n 1)"
  fi

  printf '%s' "$session_id"
}

run_codex_with_prompt() {
  local prompt="$1"
  shift
  if should_use_tty; then
    local cmd_str
    cmd_str="$(cmd_to_string "${codex_cmd[@]}" "$@")"
    script -q -e -c "$cmd_str" /dev/null <<<"$prompt"
  else
    "${codex_cmd[@]}" "$@" <<<"$prompt"
  fi
}

spawn_codex_with_prompt() {
  local pid_var="$1"
  local prompt="$2"
  local output_path="$3"
  shift 3
  if should_use_tty; then
    local cmd_str
    cmd_str="$(cmd_to_string "${codex_cmd[@]}" "$@")"
    script -q -e -c "$cmd_str" /dev/null <<<"$prompt" >"$output_path" 2>&1 &
  else
    "${codex_cmd[@]}" "$@" <<<"$prompt" >"$output_path" 2>&1 &
  fi
  printf -v "$pid_var" '%s' "$!"
}

if [[ "$infinite" == "true" ]]; then
  codex_pid=""
  tee_pid=""
  fifo=""
  first_run_output=""
  session_id=""
  cycle_count=0

  kill_tree() {
    local root_pid="$1"
    local signal_name="$2"
    local children=""

    if [[ -z "$root_pid" ]] || ! kill -0 "$root_pid" 2>/dev/null; then
      return 0
    fi

    if command -v pgrep >/dev/null 2>&1; then
      children="$(pgrep -P "$root_pid" 2>/dev/null || true)"
    else
      children="$(ps -o pid= --ppid "$root_pid" 2>/dev/null || true)"
    fi

    for child_pid in $children; do
      kill_tree "$child_pid" "$signal_name"
      kill "-$signal_name" "$child_pid" 2>/dev/null || true
    done
  }

  terminate_pid_tree() {
    local root_pid="$1"
    if [[ -z "$root_pid" ]] || ! kill -0 "$root_pid" 2>/dev/null; then
      return 0
    fi

    kill_tree "$root_pid" TERM
    kill -TERM "$root_pid" 2>/dev/null || true

    sleep 0.2

    kill_tree "$root_pid" KILL
    kill -KILL "$root_pid" 2>/dev/null || true
  }

  cleanup_infinite() {
    if [[ -n "${fifo:-}" ]]; then
      rm -f "$fifo" 2>/dev/null || true
    fi
    if [[ -n "${first_run_output:-}" ]]; then
      rm -f "$first_run_output" 2>/dev/null || true
    fi
  }

  stop_infinite() {
    terminate_pid_tree "$codex_pid"
    if [[ -n "$tee_pid" ]] && kill -0 "$tee_pid" 2>/dev/null; then
      kill -TERM "$tee_pid" 2>/dev/null || true
    fi
    exit 130
  }

  trap cleanup_infinite EXIT
  trap stop_infinite INT TERM

  prompt=""
  if [[ -n "$prompt_file" ]]; then
    if [[ ! -f "$prompt_file" ]]; then
      echo "error: file not found: $prompt_file" >&2
      exit 2
    fi
    prompt="$(cat "$prompt_file")"
  elif [[ ${#prompt_args[@]} -gt 0 ]]; then
    prompt="${prompt_args[*]}"
  else
    prompt="$(cat)"
  fi

  start_new_session() {
    local new_session_id=""

    fifo="$(mktemp)"
    rm -f "$fifo"
    mkfifo "$fifo"
    first_run_output="$(mktemp)"

    tee "$first_run_output" <"$fifo" &
    tee_pid=$!

    spawn_codex_with_prompt codex_pid "$prompt" "$fifo" -
    wait "$codex_pid"
    exit_code=$?
    codex_pid=""

    rm -f "$fifo"
    fifo=""
    wait "$tee_pid" || true
    tee_pid=""

    if [[ "$exit_code" -ne 0 ]]; then
      exit "$exit_code"
    fi

    new_session_id="$(extract_session_id_from_output "$first_run_output")"
    rm -f "$first_run_output"
    first_run_output=""
    if [[ -z "$new_session_id" ]]; then
      echo "error: unable to determine Codex session id (try adding --json)" >&2
      exit 1
    fi

    session_id="$new_session_id"
    cycle_count=1
  }

  start_new_session

  while true; do
    if [[ "$session_cycles" -gt 0 && "$cycle_count" -ge "$session_cycles" ]]; then
      start_new_session
      continue
    fi

    exit_code=0
    spawn_codex_with_prompt codex_pid "$prompt" "/dev/stdout" resume "$session_id" -
    if ! wait "$codex_pid"; then
      exit_code=$?
    fi
    codex_pid=""

    if [[ "$exit_code" -ne 0 ]]; then
      exit "$exit_code"
    fi

    cycle_count=$((cycle_count + 1))
  done
fi

if [[ -n "$prompt_file" ]]; then
  if [[ ! -f "$prompt_file" ]]; then
    echo "error: file not found: $prompt_file" >&2
    exit 2
  fi
  run_codex_with_prompt "$(cat "$prompt_file")" -
  exit $?
fi

if [[ ${#prompt_args[@]} -gt 0 ]]; then
  run_codex_with_prompt "${prompt_args[*]}" -
  exit $?
fi

exec "${codex_cmd[@]}" -
