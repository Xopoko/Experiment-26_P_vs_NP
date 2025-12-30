#!/usr/bin/env python3
"""Toy sweep for Q43: where scaled log2^5 implies the HR log2 bound.

Deterministic scan over L = floor(log2(n^2)) for small c.
"""

from __future__ import annotations

import math

C1 = 27680440320000
K = 2 * C1

C_MIN = 0
C_MAX = 12
L_MAX = 220


def ceil_sqrt(x: int) -> int:
    r = math.isqrt(x)
    return r if r * r == x else r + 1


def n_range_for_L(L: int) -> tuple[int, int]:
    low = math.isqrt(1 << L)
    if low * low < (1 << L):
        low += 1
    high = math.isqrt((1 << (L + 1)) - 1)
    return low, high


def find_last_counterexample(c: int) -> tuple[int, int] | None:
    last: tuple[int, int] | None = None
    for L in range(1, L_MAX + 1):
        n_min, n_max = n_range_for_L(L)
        n_scaled = ceil_sqrt(K * (L ** (c + 5)))
        n_hr = 16 * (L ** (c + 1))
        n_candidate = max(n_min, n_scaled)
        if n_candidate <= n_max and n_candidate < n_hr:
            last = (L, n_candidate)
    return last


def main() -> None:
    print(f"params: C_MIN={C_MIN} C_MAX={C_MAX} L_MAX={L_MAX}")
    for c in range(C_MIN, C_MAX + 1):
        last = find_last_counterexample(c)
        if last is None:
            print(f"c={c}: no counterexample up to L={L_MAX}")
        else:
            L, n = last
            print(f"c={c}: last counterexample L={L} n={n}")


if __name__ == "__main__":
    main()
