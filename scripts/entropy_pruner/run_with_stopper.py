from __future__ import annotations

import argparse
from pathlib import Path

from .model import load_model
from .sat_toy import generate_cnf, search_find_model
from .utils import seeded_rng


def main() -> int:
    parser = argparse.ArgumentParser(description="Run baseline vs pruning on toy SAT.")
    parser.add_argument("--model", default="agent/logs/entropy_model.json")
    parser.add_argument("--instances", type=int, default=30)
    parser.add_argument("--vars", type=int, default=12)
    parser.add_argument("--clauses", type=int, default=50)
    parser.add_argument("--clause_size", type=int, default=3)
    parser.add_argument("--threshold", type=float, default=0.9)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--max_nodes", type=int, default=50000)
    args = parser.parse_args()

    model_path = Path(args.model)
    model = load_model(model_path)

    rng = seeded_rng(args.seed)

    base_nodes = 0
    pruned_nodes = 0
    pruned_pruned = 0
    base_solved = 0
    pruned_solved = 0
    base_time = 0.0
    pruned_time = 0.0

    for _ in range(args.instances):
        cnf = generate_cnf(
            args.vars,
            args.clauses,
            clause_size=args.clause_size,
            seed=rng.randint(0, 1_000_000_000),
        )

        base = search_find_model(
            cnf,
            n_vars=args.vars,
            max_nodes=args.max_nodes,
            model=None,
        )
        pruned = search_find_model(
            cnf,
            n_vars=args.vars,
            max_nodes=args.max_nodes,
            model=model,
            threshold=args.threshold,
        )

        base_nodes += base.nodes
        pruned_nodes += pruned.nodes
        pruned_pruned += pruned.pruned
        base_time += base.elapsed_sec
        pruned_time += pruned.elapsed_sec

        if base.status in {"sat", "unsat"}:
            base_solved += 1
        if pruned.status in {"sat", "unsat"}:
            pruned_solved += 1

    instances = args.instances
    base_avg_nodes = base_nodes / max(1, instances)
    pruned_avg_nodes = pruned_nodes / max(1, instances)
    reduction = 0.0
    if base_avg_nodes > 0:
        reduction = 1.0 - (pruned_avg_nodes / base_avg_nodes)

    print("Run summary")
    print(f"  instances: {instances}")
    print(f"  threshold: {args.threshold:.2f}")
    print(f"  baseline_solved: {base_solved}/{instances}")
    print(f"  pruned_solved: {pruned_solved}/{instances}")
    print(f"  baseline_avg_nodes: {base_avg_nodes:.1f}")
    print(f"  pruned_avg_nodes: {pruned_avg_nodes:.1f}")
    print(f"  pruned_nodes: {pruned_pruned}")
    print(f"  node_reduction: {reduction:.2%}")
    print(f"  baseline_avg_time: {base_time / max(1, instances):.4f}s")
    print(f"  pruned_avg_time: {pruned_time / max(1, instances):.4f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
