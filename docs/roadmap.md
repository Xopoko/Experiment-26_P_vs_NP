# Roadmap

## Main track (proof complexity / Tseitin)

Goal: use switching-lemma style lower bounds for bounded-depth Frege on Tseitin(grid),
then map the obstruction to a path toward P vs NP (via proof complexity and EF/IPS).

Active focus:
- Q43 (flat local-EF(s)): evaluations + switching framework, constants and parameter checks.
- Q39 (bounded-depth Frege): isolate the XOR/Gaussian-elimination step obstruction.

Q43 reduction update (Q43.S202):
- Unfolding P-queries replaces HR depth parameter `t` with `t'=(2s+1)t`.
- If `s,t` are polylog(n) with log base 2, then `t'` stays polylog(n).
- HR parameter checks reduce to `t'<=n/16` and `s<=n/32` under the same `n_eta` recursion.
- Depends on §16.165 and §16.342 in `formal/Notes/TseitinLocalEF.lean`.
- Lean anchor: `formal/WIP/Verified/Q43.lean` (Q43_tPrime).

Q43 log2 threshold asymptotic check (Q43.S221):
- For grid size |F|=n^2, `log2 |F| >= 1` holds once `n >= 2`.
- This clears the side condition in the multiplicative threshold form.
- Lean anchor: `formal/WIP/Verified/Q43.lean` (Q43_log2_grid_ge_one).
- Next: apply it in the regime-d inequality to remove division.

Q43 log2 monotonicity in n (Q43.S239):
- For |F|=n^2, prove `log2 |F|` is monotone in n.
- Reduces to grid-size monotonicity plus `log2` monotonicity.
- Supports lifting the regime-d threshold from n0 to larger n.
- Lean anchor: `formal/WIP/Verified/Q43.lean` (Q43_log2_grid_size_mono).

Q43 gap-min bridge simplification (Q43.S278):
- Route the gap-min ratio alias through the uniform `n_k` drop lemma instead of k-lists.
- This keeps the ratio-drop witness uniform for all `k ≥ 12`.
- The bridge is now a one-line Lean proof that reuses `Q43_grid_ratio_drop_nk`.
- Lean anchor: `formal/WIP/Verified/Q43.lean` (Q43_grid_ratio_drop_nk).
- No new external sources required.

Q43 gap-min global bridge apply (Q43.S279):
- Apply the uniform `n_k` drop to the global gap-min ratio at `k=12`.
- Align `n_k + 1` with the concrete `Q43_gap_n_succ` witness via a small equality lemma.
- Removes the last dependency on the ad hoc gap witness for the global statement.
- Lean anchor: `formal/WIP/Verified/Q43.lean` (Q43_gap_min_ratio_drop_global).
- Next: wire downstream gap-min uses through the global lemma and drop obsolete k-list hooks.

Key dependencies:
- HR'22 switching lemma framework and evaluation definitions.
- Precise handling of parameters (A, c1, c2) and depth thresholds.

## Secondary track (circuit lower bounds)

Support work: relate proof-complexity barriers to circuit lower bounds and
avoid natural proofs barriers where possible.

## Formalization track (Lean 4)

The formal layer lives in `formal/` (Lean 4). Initial milestones:
1) Set up basic definitions of P/NP and reductions (align with docs/01-06).
2) Formalize core combinatorial lemmas used in proof complexity sections.
3) Prefer formal proofs; use exact citations in `docs/sources.md` for external facts.

### Formalization backlog (short list)

- **F0 (started):** definitions of languages, P, NP in `formal/PvNP/Core/Defs.lean` (mirror `docs/01`).
- **F1 (started):** many‑one reductions and NP‑complete predicate in `formal/PvNP/Core/Reductions.lean` (mirror `docs/04`).
- **F2 (in progress):** CNF/3CNF syntax and SAT in `formal/PvNP/Core/SAT.lean`; graph/clique skeleton in `formal/PvNP/Core/Graph.lean`; definitions of SAT→3SAT and 3SAT→CLIQUE in `formal/PvNP/Core/ReductionsSAT.lean`; correctness to be formalized.
- **F3:** Switching lemma skeleton and AC⁰ lower bound scaffolding (mirror `docs/10`–`docs/11`).
- **F4:** Minimal proof‑complexity utilities needed for Q39/Q43 (names to be fixed once we pick the first lemma).

## Near-term milestones (2-4 steps)

1) Q43: compare n0(A) vs 20 C n' log n' with explicit A.
2) Q39: attempt a rank/projection obstruction for XOR-step at critical depth.
