# Formal layer (Lean 4)

This directory holds the formal development. The chosen proof assistant is Lean 4.
Markdown proofs in `docs/` are **not** formal proofs; they are candidates to be ported here.

Layout:
- `PvNP/`   Core definitions and lemmas.
- `Notes/`  Long research notes kept as Lean doc-comments.

Build (if Lean is installed):

```bash
cd formal
lake build
```

Policy:
- The final theorem (P != NP or P = NP) must be fully formalized in Lean.
