#!/usr/bin/env python3
"""Toy check: gap drop aligns with log2 jump at n_k = floor(sqrt(2^(2k+1)-1))."""
from __future__ import annotations

import math


def log2_nat(n: int) -> int:
    return n.bit_length() - 1 if n > 0 else 0


def n_k(k: int) -> int:
    return math.isqrt((1 << (2 * k + 1)) - 1)


def grid_ratio(n: int) -> int:
    grid = n * n
    log = log2_nat(grid)
    if log == 0:
        raise ValueError("log2(n^2) is zero")
    return grid // (log ** 5)


def main() -> None:
    ks = list(range(12, 31))
    print("Toy check: n_k = floor(sqrt(2^(2k+1)-1))")
    print("Verify log2(n_k^2)=2k, log2((n_k+1)^2)=2k+1, and ratio drop.")
    failures = 0
    for k in ks:
        n = n_k(k)
        n1 = n + 1
        log_n = log2_nat(n * n)
        log_n1 = log2_nat(n1 * n1)
        ok_log = (log_n == 2 * k) and (log_n1 == 2 * k + 1)
        ok_ratio = grid_ratio(n1) < grid_ratio(n)
        lo = 5 * (1 << (k - 2))
        hi = 3 * (1 << (k - 1))
        in_gap = lo <= n and n1 < hi
        status = "ok" if ok_log and ok_ratio and in_gap else "fail"
        if status != "ok":
            failures += 1
        print(
            f"k={k:2d} n={n} n+1={n1} log2(n^2)={log_n} log2((n+1)^2)={log_n1} "
            f"gap=[{lo},{hi}) ratio_drop={ok_ratio} -> {status}"
        )
    if failures:
        raise SystemExit(f"failures: {failures}")


if __name__ == "__main__":
    main()
