Q43.S301-flat-eval-evaluation-statement (Proof artifact).
- Added `Q43_log2_poly_bound` to bound `log2 (n^k + 1)` by `(log2 n + 1) * k + 1` for n >= 2.
- Added `Q43_tParam_le_log2_poly_bound` to convert polynomial size bounds into t-parameter bounds.
- Extended `Q43_polyNM_log2_bounds` and `Q43_regime_d_ok_polyNM_bounds` with the explicit log2 bound.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- Note: the quasi-poly case follows from `Q43_log2_mono` and `Nat.log2_two_pow` without new lemmas.
