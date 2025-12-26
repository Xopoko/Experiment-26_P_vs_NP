# Roadmap

## Main track (proof complexity / Tseitin)

Goal: use switching-lemma style lower bounds for bounded-depth Frege on Tseitin(grid),
then map the obstruction to a path toward P vs NP (via proof complexity and EF/IPS).

Active focus:
- Q43 (flat local-EF(s)): evaluations + switching framework, constants and parameter checks.
- Q39 (bounded-depth Frege): isolate the XOR/Gaussian-elimination step obstruction.

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
3) Keep external stubs in `formal/External/` with explicit citations until replaced.

## Near-term milestones (2-4 steps)

1) Q43: compare n0(A) vs 20 C n' log n' with explicit A.
2) Q39: attempt a rank/projection obstruction for XOR-step at critical depth.
