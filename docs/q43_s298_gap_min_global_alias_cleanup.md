Q43.S298-gap-min-global-alias-cleanup (Proof artifact).
- Removed the `Q43_gap_min_ratio_k` alias and inlined `Q43_grid_ratio`.
- Dropped redundant gap-min wrapper lemmas now that the alias is gone.
- The global drop lemma now uses `Q43_grid_ratio_drop_nk` directly.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- Notes: refactor only; proof behavior unchanged.
