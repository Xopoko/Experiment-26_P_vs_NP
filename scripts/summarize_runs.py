#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description="Summarize agent run meta logs.")
    parser.add_argument(
        "--logs",
        type=Path,
        default=Path("agent/logs"),
        help="Directory with *.meta.json files",
    )
    args = parser.parse_args()

    if not args.logs.exists():
        print(f"No logs dir: {args.logs}")
        return 2

    meta_files = sorted(args.logs.glob("*.meta.json"))
    if not meta_files:
        print(f"No meta logs found in {args.logs}")
        return 0

    outcome_counts = Counter()
    item_counts = Counter()
    item_outcomes: dict[str, Counter[str]] = defaultdict(Counter)
    entropy_decisions = Counter()
    entropy_scores: list[float] = []
    entropy_signal_counts: list[int] = []

    for path in meta_files:
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue

        outcome = str(data.get("outcome", "UNKNOWN"))
        item = str(data.get("selected_item", "UNKNOWN"))

        outcome_counts[outcome] += 1
        item_counts[item] += 1
        item_outcomes[item][outcome] += 1

        entropy = data.get("entropy")
        if isinstance(entropy, dict):
            decision = entropy.get("decision")
            if isinstance(decision, str) and decision:
                entropy_decisions[decision] += 1
            score = entropy.get("score")
            if isinstance(score, (int, float)):
                entropy_scores.append(float(score))
            signals = entropy.get("signals")
            if isinstance(signals, list):
                entropy_signal_counts.append(len(signals))

    total = sum(outcome_counts.values())
    print(f"Total runs: {total}")
    print("Outcomes:")
    for outcome, count in outcome_counts.most_common():
        print(f"- {outcome}: {count}")

    print("Top items:")
    for item, count in item_counts.most_common(10):
        outcomes = ", ".join(
            f"{k}:{v}" for k, v in item_outcomes[item].most_common()
        )
        print(f"- {item}: {count} ({outcomes})")

    if entropy_scores:
        avg_score = sum(entropy_scores) / len(entropy_scores)
        print(f"Entropy avg score: {avg_score:.2f} (n={len(entropy_scores)})")
    if entropy_signal_counts:
        avg_signals = sum(entropy_signal_counts) / len(entropy_signal_counts)
        print(f"Entropy avg signals: {avg_signals:.1f}")
    if entropy_decisions:
        decisions = ", ".join(f"{k}:{v}" for k, v in entropy_decisions.most_common())
        print(f"Entropy decisions: {decisions}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
