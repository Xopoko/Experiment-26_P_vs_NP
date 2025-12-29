# Formal layer (Lean 4)

This directory holds the formal development. The chosen proof assistant is Lean 4.
Markdown proofs in `docs/` are **not** formal proofs; they are candidates to be ported here.

Layout:
- `PvNP/Core/`   Authoritative definitions and lemmas (no `sorry`/`axiom`).
- `WIP/Verified/` Work-in-progress Lean proofs (no `sorry`/`axiom`).
- `WIP/Scratch/`  Scratch space (placeholders allowed; not proof artifacts).
- `Notes/`       Long research notes kept as Lean doc-comments.
- `Checks/`      Lean checks (axioms audit).

Build (if Lean is installed):

```bash
cd formal
lake build PvNP
```

Optional:

```bash
lake build Notes
lake build WIP
```

Policy:
- The final theorem (P != NP or P = NP) must be fully formalized in Lean and live in `PvNP/Core/`.
