# Formal layer (Lean 4)

This directory holds the formal development. The chosen proof assistant is Lean 4.
Markdown proofs in `docs/` are **not** formal proofs; they are candidates to be ported here.

Layout:
- `PvNP/Core/`   Authoritative definitions and lemmas (no `sorry`/`axiom`).
- `WIP/`         Work-in-progress Lean proofs (can contain placeholders).
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

Mathlib caches (recommended if you start importing `Mathlib.*`):

```bash
cd formal
lake exe cache get
```

Policy:
- The final theorem (P != NP or P = NP) must be fully formalized in Lean and live in `PvNP/Core/`.
