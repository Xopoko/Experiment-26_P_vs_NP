## 0. Agreement on "formal verifiability"

In this notebook, "formally verifiable" means:

1. **Computation model fixed** and unified agreement on polynomiality
   (robustness between standard models is specified explicitly).
2. Each statement is written as a **theorem/lemma** with explicit premises.
3. For each lemma: **full proof** (or explicitly marked *"cited"* with exact reference).
4. For constructions/reductions: explicit algorithm and proof of correctness + time estimate.
5. For "new ideas": required sections **counterexamples/edge cases**
   and **testing for barriers** (relativization, natural proofs, algebrization).
6. For notes *"quoted"*: the exact link should be in the "Sources" Section
   and in `../resources/manifest.tsv` (if possible - downloaded PDF in `../resources/downloads/`).
7. For test code: reproducible run without Jupyter: `scripts/verify_all.sh`
   (includes `verify_notebook.py` and formal build; by default requires `lake`,
   admission is possible only with `REQUIRE_LEAN=0`).
8. The formal layer lives in `formal/` (Lean 4).
9. External statements are recorded only as **exact references** in `docs/sources.md`
   (without adding axioms/stubs).
10. In Markdown we write **formally stated** proofs (complete and hand-verifiable),
    but this is not considered formal verification before transfer to `formal/`.
