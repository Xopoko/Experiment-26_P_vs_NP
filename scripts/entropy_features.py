#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_POLICY = Path(__file__).with_name("stopper_policy.json")
OPEN_QUESTIONS = REPO_ROOT / "docs" / "open_questions.md"
AGENT_BRIEF = REPO_ROOT / "docs" / "agent_brief.md"
LOGS_DIR = REPO_ROOT / "agent" / "logs"

_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")


def _read_lines(path: Path) -> list[str]:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []


def _extract_backticked_meta(lines: list[str], key: str) -> str | None:
    needle = f"`{key}:`"
    for line in lines:
        if needle not in line:
            continue
        return line.split(needle, 1)[1].strip()
    return None


def _extract_qid(selected_item: str, step_id: str) -> str | None:
    for text in (selected_item, step_id):
        if not text:
            continue
        match = re.search(r"Q\d{1,4}", text)
        if match:
            return match.group(0)
    return None


def _find_item_block(lines: list[str], qid: str) -> list[str] | None:
    start = None
    for i, line in enumerate(lines):
        if line.startswith("- [") and f"**{qid}" in line:
            start = i
            break
    if start is None:
        return None
    block = [lines[start]]
    for j in range(start + 1, len(lines)):
        line = lines[j]
        if line.startswith("- ["):
            break
        block.append(line)
    return block


def _parse_int(token: str | None) -> int | None:
    if token is None:
        return None
    raw = token.strip().split()[0] if token.strip() else ""
    if not raw:
        return None
    if not raw.lstrip("-").isdigit():
        return None
    return int(raw)


def _normalize_reason(reason: str | None) -> str:
    if reason is None:
        return ""
    token = reason.strip().lower()
    if token in {"", "none", "n/a", "na", "unknown"}:
        return ""
    return token


def load_policy(path: Path) -> dict[str, object]:
    raw = path.read_text(encoding="utf-8")
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError("policy JSON must be an object")
    return data


def _load_meta_logs() -> list[dict[str, object]]:
    if not LOGS_DIR.exists():
        return []
    files = sorted(LOGS_DIR.glob("*.meta.json"), key=lambda p: p.stat().st_mtime, reverse=True)
    logs: list[dict[str, object]] = []
    for path in files:
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        logs.append(data)
    return logs


def compute_entropy(*, contract_path: Path, mode: str, policy_path: Path) -> dict[str, object]:
    signals: list[str] = []

    try:
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise SystemExit(f"missing contract file: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid contract JSON: {exc}") from exc

    selected_item = str(contract.get("selected_item", "")).strip()
    step_id = str(contract.get("step_id", "")).strip()
    if not selected_item:
        signals.append("missing:selected_item")
    if not step_id or not _STEP_ID_RE.match(step_id):
        signals.append("missing:step_id")

    qid = _extract_qid(selected_item, step_id)
    if not qid:
        signals.append("missing:qid")

    policy = load_policy(policy_path)
    policy_version = str(policy.get("policy_version", "unknown"))
    weights = policy.get("weights", {})
    if not isinstance(weights, dict):
        weights = {}
        signals.append("missing:weights")

    item_block = None
    if qid:
        item_block = _find_item_block(_read_lines(OPEN_QUESTIONS), qid)
        if item_block is None:
            signals.append("missing:open_questions_item")
    else:
        signals.append("missing:open_questions_item")

    attempts = 0
    if item_block:
        attempts_val = _parse_int(_extract_backticked_meta(item_block, "Attempts"))
        if attempts_val is None:
            signals.append("missing:Attempts")
        else:
            attempts = attempts_val
    else:
        signals.append("missing:Attempts")

    brief_lines = _read_lines(AGENT_BRIEF)
    last_failure_reason = _normalize_reason(_extract_backticked_meta(brief_lines, "LastFailureReason"))
    if not last_failure_reason:
        signals.append("missing:LastFailureReason")

    do_not_repeat_raw = _extract_backticked_meta(brief_lines, "Do-not-repeat (next 2 runs)")
    do_not_repeat = [s.strip() for s in (do_not_repeat_raw or "").split(",") if s.strip()]
    if not do_not_repeat_raw:
        signals.append("missing:Do-not-repeat")

    cooldown_hit = 1 if step_id and step_id in do_not_repeat else 0

    meta_logs = _load_meta_logs()
    if not meta_logs:
        signals.append("missing:meta_logs")

    previous_failure = ""
    for meta in meta_logs:
        previous_failure = _normalize_reason(
            str(meta.get("last_failure_reason", "")) or str(meta.get("failure_reason", ""))
        )
        if previous_failure:
            break

    repeat_failure = 0
    if last_failure_reason and previous_failure:
        repeat_failure = 1 if last_failure_reason == previous_failure else 0
    elif last_failure_reason or previous_failure:
        signals.append("missing:previous_failure_reason")

    zero_infogain_streak = 0
    if meta_logs:
        missing_info_gain = False
        for meta in meta_logs:
            val = meta.get("info_gain", meta.get("last_info_gain"))
            if val is None:
                missing_info_gain = True
                break
            try:
                gain = int(val)
            except (TypeError, ValueError):
                missing_info_gain = True
                break
            if gain == 0:
                zero_infogain_streak += 1
            else:
                break
        if missing_info_gain:
            signals.append("missing:info_gain")
    else:
        signals.append("missing:info_gain")

    recent_verify_fail = 0
    if meta_logs:
        verify_code = meta_logs[0].get("verify_exit_code")
        if verify_code is None:
            signals.append("missing:verify_exit_code")
        else:
            try:
                recent_verify_fail = 1 if int(verify_code) != 0 else 0
            except (TypeError, ValueError):
                signals.append("missing:verify_exit_code")
    else:
        signals.append("missing:verify_exit_code")

    features = {
        "attempts": attempts,
        "repeat_failure": repeat_failure,
        "zero_infogain_streak": zero_infogain_streak,
        "cooldown_hit": cooldown_hit,
        "recent_verify_fail": recent_verify_fail,
    }

    for name, value in features.items():
        if name == "repeat_failure" and value:
            signals.append("repeat_failure")
        if name == "zero_infogain_streak":
            if value >= 2:
                signals.append("zero_infogain_streak>=2")
            elif value == 1:
                signals.append("zero_infogain_streak=1")
        if name == "cooldown_hit" and value:
            signals.append("cooldown_hit")
        if name == "recent_verify_fail" and value:
            signals.append("recent_verify_fail")

    score = 0.0
    for name, value in features.items():
        weight = weights.get(name)
        if weight is None:
            signals.append(f"missing:weight:{name}")
            continue
        try:
            score += float(weight) * float(value)
        except (TypeError, ValueError):
            signals.append(f"missing:weight:{name}")

    payload = {
        "policy_version": policy_version,
        "mode": mode,
        "features": features,
        "signals": signals,
        "score": round(score, 4),
    }
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Compute entropy features for a run.")
    parser.add_argument("--contract", required=True, help="Path to run contract JSON")
    parser.add_argument("--mode", choices=["pre", "post"], default="pre")
    parser.add_argument("--policy", default=str(DEFAULT_POLICY), help="Path to policy JSON")
    parser.add_argument("--out", default="", help="Optional output path")
    args = parser.parse_args()

    contract_path = Path(args.contract)
    if not contract_path.exists():
        print(f"missing contract file: {contract_path}", file=sys.stderr)
        return 2

    policy_path = Path(args.policy)
    if not policy_path.exists():
        print(f"missing policy file: {policy_path}", file=sys.stderr)
        return 2

    payload = compute_entropy(contract_path=contract_path, mode=args.mode, policy_path=policy_path)
    raw = json.dumps(payload, indent=2, sort_keys=True)

    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(raw + "\n", encoding="utf-8")

    print(raw)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
