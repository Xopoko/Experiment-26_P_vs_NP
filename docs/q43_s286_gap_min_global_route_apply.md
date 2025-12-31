Q43.S286-gap-min-global-route-apply (Proof artifact).
- Removed the redundant k=12 gap-min lemma that expanded `Q43_gap_min_ratio_k`.
- Keep `Q43_gap_min_ratio_le_all` as the single gap-scan statement.
- This avoids extra k-list rewrites when referencing the gap-min lower bound.
- Lean anchor: `formal/WIP/Verified/Q43.lean`.
- Oracle: `python3 scripts/toy_q43_gap_sqrt2.py` (k=12..104 ok).
