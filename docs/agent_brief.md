# Agent brief (bounded working memory)

Rule: this file is the agent's "RAM". It **shouldn't grow**
(the limit is checked in `scripts/verify_all.sh`). Update it by **replacement/compression**,
and not by adding to endless lists.

## Anti-loop (update, don't bloat)

- `LastStepID:` Q43.S298-gap-min-global-alias-cleanup
- `Do-not-repeat (next 2 runs):` Q43.S298-gap-min-global-alias-cleanup, Q43.S297-gap-min-global-consolidate-klist
- `Last InfoGain:` 0

## Current direction (keep 1-2 lines)

Q39: contiguous alt-shifts now through alt117; next step is classification or barrier.
Q43: inlined the gap-min alias; next formalize the Q43.S137 evaluation statement.

## What has already been done (do not repeat)

- ROABP canonicalization multilinearization for CNF gives $\mathrm{P}=\mathrm{NP}$ (barrier lemmas 15.7.4* in `docs/15_proof_complexity.md`).
- PIT-axioms  EF p-simulates IPS; basic encodings (CNF->3CNF + $g$, TseitinEval, counters) already in 16.x.
- Tseitin: Frege poly (16.91); bounded-depth lower bounds (Hastad'20, 16.92) + all-graphs extension (GIRS'19, 16.97); missing Gauss step noted in Hastad-Risse Section 1.2 (16.122). Cor. 34: bounded-depth Frege  tree-like Res quasi-poly (16.98); EF poly (16.88); PC: $\\mathbb F_2$ easy (16.89), char$\\ne2$ hard (16.90).

## Active "unique" tasks (select one per run)

- Q39 from `docs/open_questions.md` (next alt-shift for contiguous blocks).
- Q43 from `docs/open_questions.md` (lift the threshold without global monotonicity of the relationship).

## Experiment register (max 12 items; overwrite old ones)

- E01: Formalization of PIT axioms (GP14 Def. 1.7) and connection with SoundnessIPS -> EF sim IPS (see 15.7.3).
- E02: Canonization barrier $\mathrm{ML}(P_\varphi)$ -> ROABP (see 15.7.4*).
- E03: LogLog trick for bounded quantifiers/truth tables (toy steps in 16.x).
- E04: Counterexample "equivalence CNF->3CNF" and correct mode equisatisfiable + explicit $g$ + linear counting (15.7.3c-d; 16.78).
- E05: Tseitin encoding $\mathrm{Eval}(C,x)$ gives 3-CNF $O(s)$ (toy steps 16.x).
- E07: Planar‑3‑SAT → Planar‑3‑SAT(≤4‑occ) (16.83–16.84).
- E08: Tseitin($G,\\chi$): parity certificate of unsatisfiability + 3CNF for 3regular graphs (16.85).
- E09: Tseitin on boundeddegree expanders: $W\\ge e(G)-1$ and $S\\ge 2^{(e(G)-k-1)^2/|E|}$ (16.86).
- E10: Explicit bounded-occ Tseitin-family on 3-regular expanders (16.87).
- E11: Tseitin summary: Frege poly (16.91), depth vs size (16.92-16.99), EF via XOR (16.88), PC: $\\mathbb F_2$ easy (16.89), $\\mathrm{char}\\ne 2$ hard (16.90).

## Lenses (keep the last 5; update, do not increase)

Latest:Specification/definitions audit->Compression/canonization->Automation/tactic engineering->Compression/canonization->Automation/tactic engineering
