Q43.S288-gap-min-global-prune-klist-21-30 (Proof artifact).
- Pruned the unused k=21..30 gap-range and ratio-drop witness blocks.
- Removed the matching n_k = gap_n lemmas for k=21..30.
- Keeps k=12 as the base case and k>=31 for the remaining sweep.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- Notes: refactor only; proof behavior unchanged.
