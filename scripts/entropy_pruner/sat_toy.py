from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Iterable, Sequence

from .features import compute_features, canonical_key
from .utils import seeded_rng


Clause = list[int]
CNF = list[Clause]


@dataclass
class SearchResult:
    status: str
    nodes: int
    pruned: int
    elapsed_sec: float


@dataclass
class DatasetResult:
    rows: list[tuple[dict[str, float], int]]
    nodes: int
    truncated: bool


def generate_cnf(
    n_vars: int,
    n_clauses: int,
    *,
    clause_size: int = 3,
    seed: int | None = None,
) -> CNF:
    rng = seeded_rng(seed)
    clauses: CNF = []
    for _ in range(n_clauses):
        vars_chosen = rng.sample(range(1, n_vars + 1), k=min(clause_size, n_vars))
        clause: Clause = []
        for var in vars_chosen:
            sign = 1 if rng.random() < 0.5 else -1
            clause.append(sign * var)
        clauses.append(clause)
    return clauses


def simplify_cnf(clauses: CNF, var: int, value: bool) -> CNF:
    true_lit = var if value else -var
    false_lit = -true_lit
    new_clauses: CNF = []
    for clause in clauses:
        if true_lit in clause:
            continue
        new_clause = [lit for lit in clause if lit != false_lit]
        new_clauses.append(new_clause)
    return new_clauses


def propagate_units(clauses: CNF, assignment: dict[int, bool]) -> tuple[CNF, dict[int, bool], bool]:
    clauses = [list(clause) for clause in clauses]
    assignment = dict(assignment)
    while True:
        unit_lit = None
        for clause in clauses:
            if len(clause) == 0:
                return clauses, assignment, True
            if len(clause) == 1:
                unit_lit = clause[0]
                break
        if unit_lit is None:
            break
        var = abs(unit_lit)
        val = unit_lit > 0
        if var in assignment and assignment[var] != val:
            return clauses, assignment, True
        assignment[var] = val
        clauses = simplify_cnf(clauses, var, val)
    return clauses, assignment, False


def pick_var(clauses: CNF, assignment: dict[int, bool]) -> int | None:
    counts: dict[int, int] = {}
    for clause in clauses:
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                continue
            counts[var] = counts.get(var, 0) + 1
    if not counts:
        return None
    return max(counts.items(), key=lambda item: item[1])[0]


def collect_labeled_nodes(
    clauses: CNF,
    *,
    n_vars: int,
    max_nodes: int | None = None,
) -> DatasetResult:
    rows: list[tuple[dict[str, float], int]] = []
    nodes = 0
    truncated = False
    seen: set[tuple[tuple[int, ...], ...]] = set()

    def solve(curr: CNF, assignment: dict[int, bool], depth: int, parent: CNF | None) -> bool | None:
        nonlocal nodes, truncated
        if max_nodes is not None and nodes >= max_nodes:
            truncated = True
            return None
        curr, assignment, conflict = propagate_units(curr, assignment)
        key = canonical_key(curr)
        features = compute_features(curr, parent=parent, depth=depth, seen=seen, n_vars=n_vars)
        seen.add(key)
        nodes += 1

        if conflict:
            rows.append((features, 1))
            return False
        if not curr:
            rows.append((features, 0))
            return True

        var = pick_var(curr, assignment)
        if var is None:
            rows.append((features, 0))
            return True

        left = simplify_cnf(curr, var, True)
        res_left = solve(left, {**assignment, var: True}, depth + 1, curr)
        if res_left is True:
            rows.append((features, 0))
            return True

        right = simplify_cnf(curr, var, False)
        res_right = solve(right, {**assignment, var: False}, depth + 1, curr)

        if res_left is None or res_right is None:
            return None

        result = bool(res_left or res_right)
        rows.append((features, 0 if result else 1))
        return result

    solve(clauses, {}, 0, None)
    return DatasetResult(rows=rows, nodes=nodes, truncated=truncated)


def search_find_model(
    clauses: CNF,
    *,
    n_vars: int,
    max_nodes: int | None = None,
    model: object | None = None,
    threshold: float = 0.9,
) -> SearchResult:
    nodes = 0
    pruned = 0
    seen: set[tuple[tuple[int, ...], ...]] = set()
    start = time.time()

    def predict_unsat(feats: dict[str, float]) -> float:
        if model is None:
            return 0.0
        return float(model.predict_proba(feats))

    def dfs(curr: CNF, assignment: dict[int, bool], depth: int, parent: CNF | None) -> str:
        nonlocal nodes, pruned
        if max_nodes is not None and nodes >= max_nodes:
            return "unknown"
        curr, assignment, conflict = propagate_units(curr, assignment)
        key = canonical_key(curr)
        feats = compute_features(curr, parent=parent, depth=depth, seen=seen, n_vars=n_vars)
        seen.add(key)
        nodes += 1

        if conflict:
            return "unsat"
        if not curr:
            return "sat"

        if model is not None:
            if predict_unsat(feats) >= threshold:
                pruned += 1
                return "pruned"

        var = pick_var(curr, assignment)
        if var is None:
            return "sat"

        left = simplify_cnf(curr, var, True)
        res_left = dfs(left, {**assignment, var: True}, depth + 1, curr)
        if res_left == "sat":
            return "sat"

        right = simplify_cnf(curr, var, False)
        res_right = dfs(right, {**assignment, var: False}, depth + 1, curr)
        if res_right == "sat":
            return "sat"

        if res_left in {"unknown", "pruned"} or res_right in {"unknown", "pruned"}:
            return "unknown"
        return "unsat"

    status = dfs(clauses, {}, 0, None)
    elapsed = time.time() - start
    return SearchResult(status=status, nodes=nodes, pruned=pruned, elapsed_sec=elapsed)
