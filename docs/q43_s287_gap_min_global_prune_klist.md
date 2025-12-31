Q43.S287-gap-min-global-prune-klist (Proof artifact).
- Pruned the unused k=13..20 gap-range and ratio-drop witness blocks.
- Removed the matching n_k = gap_n lemmas for k=13..20.
- Keeps k=12 as the base case and k>=21 for the remaining sweep.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- Notes: this is a refactor only; proof behavior is unchanged.
