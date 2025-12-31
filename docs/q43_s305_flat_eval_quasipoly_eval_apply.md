Q43.S305-flat-eval-quasipoly-eval-apply (Proof artifact).
- Added `Q43_quasipoly_grid_eval_bounds` to bundle quasi-poly grid bounds for `N` and lineMax.
- Uses `Q43_tParam_lineMax_le_polylog_of_quasipoly_grid` and log2 monotonicity to fix the M/N regime.
- Added `[simp]` lemma `Q43_tParam_lineMax_le_polylog_of_quasipoly_grid_twice` for the scaled `2*log2|F|` form.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- This applies the grid specialization inside the flat evaluation parameter statement.
