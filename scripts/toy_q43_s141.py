#!/usr/bin/env python3
"""Toy check for poly M vs exp(n^alpha) threshold (Q43.S141)."""
from __future__ import annotations

import math


def depth_for_n(n: int) -> int:
    if n < 4:
        return 2
    log2n = math.log2(n)
    log2log2n = math.log2(log2n)
    d = int(log2n / log2log2n)
    return max(2, d)


def alpha_for_d(d: int) -> float:
    return 1.0 / d - 1.0 / (d * (d - 1))


def compare(n: int, k: int, d: int) -> tuple[bool, bool, float, float, float]:
    alpha = alpha_for_d(d)
    rhs = n ** alpha
    logn = math.log(n)
    log2n = math.log2(n)
    lhs_e = k * logn
    lhs_2 = k * log2n
    ok_e = lhs_e <= rhs
    ok_2 = lhs_2 <= rhs
    return ok_e, ok_2, rhs, lhs_e, lhs_2


def main() -> None:
    n_vals = [2 ** t for t in (8, 12, 16, 20, 24, 28, 32)]
    k_vals = [1, 2, 4, 8]
    print("Toy check: M = n^k vs exp(n^alpha), alpha = 1/d - 1/(d(d-1))")
    print("exp base e uses ln; exp base 2 uses log2 (threshold is smaller if base=2).")
    for n in n_vals:
        d = depth_for_n(n)
        alpha = alpha_for_d(d)
        print(f"n={n} d={d} alpha={alpha:.6f} n^alpha={n ** alpha:.3f}")
        for k in k_vals:
            ok_e, ok_2, rhs, lhs_e, lhs_2 = compare(n, k, d)
            status_e = "ok" if ok_e else "fail"
            status_2 = "ok" if ok_2 else "fail"
            print(
                f"  k={k}: k*ln n={lhs_e:.3f} vs n^alpha={rhs:.3f} -> exp_e {status_e}; "
                f"k*log2 n={lhs_2:.3f} -> exp2 {status_2}"
            )


if __name__ == "__main__":
    main()
