from __future__ import annotations

import argparse
import csv
from pathlib import Path

from .features import FEATURE_KEYS
from .sat_toy import collect_labeled_nodes, generate_cnf
from .utils import seeded_rng


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy SAT dataset for entropy-pruner.")
    parser.add_argument("--out", default="agent/logs/entropy_dataset.csv")
    parser.add_argument("--instances", type=int, default=30)
    parser.add_argument("--vars", type=int, default=12)
    parser.add_argument("--clauses", type=int, default=50)
    parser.add_argument("--clause_size", type=int, default=3)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--max_nodes_per_instance", type=int, default=20000)
    args = parser.parse_args()

    rng = seeded_rng(args.seed)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    rows = []
    total_nodes = 0
    truncated = 0
    for i in range(args.instances):
        cnf = generate_cnf(
            args.vars,
            args.clauses,
            clause_size=args.clause_size,
            seed=rng.randint(0, 1_000_000_000),
        )
        result = collect_labeled_nodes(
            cnf,
            n_vars=args.vars,
            max_nodes=args.max_nodes_per_instance,
        )
        total_nodes += result.nodes
        if result.truncated:
            truncated += 1
        rows.extend(result.rows)

    if not rows:
        print("No rows collected; try increasing max_nodes_per_instance.")
        return 1

    fieldnames = FEATURE_KEYS + ["label_unsat"]
    with out_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for features, label in rows:
            row = {key: float(features[key]) for key in FEATURE_KEYS}
            row["label_unsat"] = int(label)
            writer.writerow(row)

    unsat = sum(1 for _, label in rows if label == 1)
    sat = len(rows) - unsat
    print("Dataset summary")
    print(f"  instances: {args.instances}")
    print(f"  nodes: {total_nodes}")
    print(f"  rows: {len(rows)} (sat {sat}, unsat {unsat})")
    print(f"  truncated_instances: {truncated}")
    print(f"  out: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
