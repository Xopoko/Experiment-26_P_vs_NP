# Formal layer (Lean 4)

This directory holds the formal development. The chosen proof assistant is Lean 4.
Markdown proofs in `docs/` are **not** formal proofs; they are candidates to be ported here.

Layout:
- `PvNP/`   Core definitions and lemmas.
- `External/`  Temporary external stubs (ASSUMPTION) with exact citations.

Build (if Lean is installed):

```bash
cd formal
lake build
```

Policy:
- The final theorem (P != NP or P = NP) must not depend on any ASSUMPTION.
- External stubs must be replaced by formal proofs before claiming completion.
- The `External` library is compiled by `lake build` but should remain dependency-free.

Current stubs:
- `External/Barriers.lean`
- `External/NPCompleteness.lean`
