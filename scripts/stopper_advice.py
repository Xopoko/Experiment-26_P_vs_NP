#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

import entropy_features  # noqa: E402


DEFAULT_POLICY = ROOT / "stopper_policy.json"


def _decision(entropy: dict[str, object], threshold: float) -> str:
    features = entropy.get("features")
    cooldown_hit = 0
    if isinstance(features, dict):
        try:
            cooldown_hit = int(features.get("cooldown_hit", 0))
        except (TypeError, ValueError):
            cooldown_hit = 0
    score = float(entropy.get("score", 0.0))
    if cooldown_hit == 1 or score >= threshold:
        return "STOP"
    return "CONTINUE"


def main() -> int:
    parser = argparse.ArgumentParser(description="Suggest STOP/CONTINUE from entropy features.")
    parser.add_argument("--contract", required=True, help="Path to run contract JSON")
    parser.add_argument("--mode", choices=["pre", "post"], default="pre")
    parser.add_argument("--policy", default=str(DEFAULT_POLICY), help="Path to policy JSON")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    args = parser.parse_args()

    policy_path = Path(args.policy)
    if not policy_path.exists():
        print(f"missing policy file: {policy_path}", file=sys.stderr)
        return 2

    policy = entropy_features.load_policy(policy_path)
    threshold = policy.get("threshold", 1.0)
    try:
        threshold_val = float(threshold)
    except (TypeError, ValueError):
        threshold_val = 1.0

    entropy = entropy_features.compute_entropy(
        contract_path=Path(args.contract),
        mode=args.mode,
        policy_path=policy_path,
    )

    decision = _decision(entropy, threshold_val)

    payload = {
        **entropy,
        "threshold": threshold_val,
        "decision": decision,
    }

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        signals = payload.get("signals", [])
        if not isinstance(signals, list):
            signals = []
        score = payload.get("score", 0.0)
        print(f"Policy: {payload.get('policy_version', 'unknown')}")
        print(f"Decision: {decision}")
        print(f"Score: {score} (threshold {threshold_val})")
        print("Signals: " + (", ".join(signals) if signals else "none"))
        if decision == "STOP":
            print("Suggested action: mark BLOCKED/Barrier, set NextStepID, stop.")
        else:
            print("Suggested action: continue with the planned artifact.")

    return 42 if decision == "STOP" else 0


if __name__ == "__main__":
    raise SystemExit(main())
