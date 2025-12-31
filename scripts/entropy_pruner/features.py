from __future__ import annotations

from typing import Iterable, Sequence

from .utils import compress_ratio, entropy_from_counts

FEATURE_KEYS = [
    "n_vars",
    "n_clauses",
    "n_literals",
    "active_vars",
    "assigned_ratio",
    "unit_clause_ratio",
    "binary_clause_ratio",
    "pure_literal_ratio",
    "clause_len_entropy",
    "var_occ_entropy",
    "compress_ratio",
    "repeat_flag",
    "depth",
    "delta_clauses",
    "delta_literals",
    "delta_units",
]


def canonical_key(clauses: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    normalized = [tuple(sorted(clause, key=lambda lit: (abs(lit), lit))) for clause in clauses]
    normalized.sort()
    return tuple(normalized)


def canonical_str(clauses: Sequence[Sequence[int]]) -> str:
    parts = []
    for clause in canonical_key(clauses):
        parts.append(",".join(str(lit) for lit in clause))
    return ";".join(parts)


def _literal_stats(
    clauses: Sequence[Sequence[int]],
    n_vars: int,
) -> tuple[int, int, int, int, int, list[int], int]:
    n_clauses = len(clauses)
    n_literals = 0
    unit_count = 0
    binary_count = 0
    var_counts = [0 for _ in range(n_vars)]
    var_signs: dict[int, set[int]] = {}
    for clause in clauses:
        clen = len(clause)
        n_literals += clen
        if clen == 1:
            unit_count += 1
        elif clen == 2:
            binary_count += 1
        for lit in clause:
            var = abs(lit)
            if 1 <= var <= n_vars:
                var_counts[var - 1] += 1
            sign = 1 if lit > 0 else -1
            var_signs.setdefault(var, set()).add(sign)
    active_vars = sum(1 for count in var_counts if count > 0)
    pure_vars = sum(1 for signs in var_signs.values() if len(signs) == 1)
    return n_clauses, n_literals, unit_count, binary_count, active_vars, var_counts, pure_vars


def clause_len_entropy(clauses: Sequence[Sequence[int]]) -> float:
    if not clauses:
        return 0.0
    max_len = max(len(c) for c in clauses)
    counts = [0 for _ in range(max_len + 1)]
    for clause in clauses:
        counts[len(clause)] += 1
    return entropy_from_counts(counts)


def var_occ_entropy(var_counts: Iterable[int]) -> float:
    return entropy_from_counts(var_counts)


def compute_features(
    clauses: Sequence[Sequence[int]],
    *,
    parent: Sequence[Sequence[int]] | None = None,
    depth: int = 0,
    seen: set[tuple[tuple[int, ...], ...]] | None = None,
    n_vars: int | None = None,
) -> dict[str, float]:
    if n_vars is None:
        n_vars = 0
        for clause in clauses:
            for lit in clause:
                n_vars = max(n_vars, abs(lit))

    key = canonical_key(clauses)
    repeat_flag = 1.0 if seen is not None and key in seen else 0.0

    n_clauses, n_literals, unit_count, binary_count, active_vars, var_counts, pure_vars = _literal_stats(
        clauses, n_vars
    )
    assigned_ratio = 0.0 if n_vars == 0 else (n_vars - active_vars) / n_vars
    unit_ratio = 0.0 if n_clauses == 0 else unit_count / n_clauses
    binary_ratio = 0.0 if n_clauses == 0 else binary_count / n_clauses
    pure_ratio = 0.0 if active_vars == 0 else pure_vars / active_vars

    clause_entropy = clause_len_entropy(clauses)
    var_entropy = var_occ_entropy(var_counts)
    c_ratio = compress_ratio(canonical_str(clauses))

    delta_clauses = 0.0
    delta_literals = 0.0
    delta_units = 0.0
    if parent is not None:
        p_n_clauses, p_n_literals, p_unit_count, _, _, _, _ = _literal_stats(parent, n_vars)
        delta_clauses = p_n_clauses - n_clauses
        delta_literals = p_n_literals - n_literals
        delta_units = p_unit_count - unit_count

    return {
        "n_vars": float(n_vars),
        "n_clauses": float(n_clauses),
        "n_literals": float(n_literals),
        "active_vars": float(active_vars),
        "assigned_ratio": float(assigned_ratio),
        "unit_clause_ratio": float(unit_ratio),
        "binary_clause_ratio": float(binary_ratio),
        "pure_literal_ratio": float(pure_ratio),
        "clause_len_entropy": float(clause_entropy),
        "var_occ_entropy": float(var_entropy),
        "compress_ratio": float(c_ratio),
        "repeat_flag": float(repeat_flag),
        "depth": float(depth),
        "delta_clauses": float(delta_clauses),
        "delta_literals": float(delta_literals),
        "delta_units": float(delta_units),
    }
