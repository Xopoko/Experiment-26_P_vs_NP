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

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
