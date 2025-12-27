# Project Architecture (P vs NP)

This document describes the current structure, flows, and control points of the repo so you can see
where to improve it.

## Goals and invariants

- Proof-first: the only authoritative results are in `formal/`.
- Docs are navigation + reasoning; they are not proofs.
- One agent run = one checkable artifact.
- No notebooks: the project is Lean-first and CLI-verified.
- Stable, bounded operational state (short prompts, bounded agent brief).

## Top-level map

```mermaid
flowchart TD
  A[AGENTS.md\nprotocol + guardrails]
  B[scripts/agent_prompt.txt\nsingle-line prompt]
  C[agent/run.sh\nrunner + logs]
  D[agent/codex-run.sh\ncodex exec wrapper]
  E[agent/logs/*.log\nper-run logs]

  F[P_vs_NP.md\nindex]
  G[docs/*\nshort theory + queue]
  H[docs/open_questions.md\nactive queue]
  I[docs/agent_brief.md\nbounded memory]

  J[formal/PvNP/*\nLean core]
  K[formal/Notes/*\nLean notes]
  L[formal/lakefile.lean\nPaperproof dep]

  M[resources/manifest.tsv\nbibliography index]
  N[resources/downloads/*\nPDF/HTML store]
  O[resources/text_cache/*\noptional cache]
  P[scripts/verify_all.sh\nCI gate]
  Q[scripts/verify_notebook.py\nstructure checks]

  A --> B --> C --> D --> E
  F --> G
  G --> H
  G --> I
  H --> J
  G --> K
  L --> J
  M --> N
  N --> O
  P --> Q
  P --> J
```

## Directory roles

- `AGENTS.md` — canonical agent protocol and constraints.
- `P_vs_NP.md` — short top-level index + links.
- `docs/` — structured written theory; kept short; history is in git.
  - `docs/open_questions.md` — active queue; each item has `StepID`, `NextStepID`, `LeanTarget`.
  - `docs/agent_brief.md` — bounded working memory to avoid loops.
  - `docs/roadmap.md`, `docs/sources.md` — route and citations.
- `formal/` — Lean 4 proof layer.
  - `formal/PvNP/` — definitions/lemmas that are meant to be real proofs.
  - `formal/Notes/` — research notes as Lean doc-comments (not proofs).
  - `formal/lakefile.lean` — depends on `Paperproof`.
- `agent/` — runner wrappers around Codex CLI.
- `scripts/` — verification and tooling (checks, arXiv search).
- `resources/` — bibliography + downloaded PDFs + optional text cache.

## Agent execution flow

```mermaid
flowchart TD
  A[agent/run.sh] --> B{REQUIRE_CLEAN?}
  B -->|yes| C[git clean check]
  B -->|no| D[skip check]
  C --> E[log header + lock]
  D --> E
  E --> F[agent/codex-run.sh\ncodex exec/resume]
  F --> G[agent/logs/RUN_ID.log]
  G --> H[agent/logs/latest.log symlink]
```

### Runner behavior

- `agent/run.sh` sets defaults and writes to `agent/logs/`.
- `agent/codex-run.sh` wraps `codex exec`, supports `--infinite`, and can use a pseudo‑TTY.
- `CODEX_TTY` (default `auto`) controls color/TTY behavior:
  - `CODEX_TTY=1` force pseudo‑TTY.
  - `CODEX_TTY=0` disable pseudo‑TTY.

### Runner configuration (env vars)

- `PROMPT_FILE`, `LOG_DIR`, `RUN_ID`, `LOG_FILE`
- `REQUIRE_CLEAN=1` to require a clean git worktree
- `CODEX_TTY` to control colored output

## Verification pipeline

```mermaid
flowchart TD
  A[scripts/verify_all.sh] --> B[scripts/verify_notebook.py]
  B --> C[docs structure checks\nopen_questions + agent_brief]
  B --> D[resources hygiene\nmanifest vs downloads]
  B --> E[prompt single-line check]
  A --> F{Lean available?}
  F -->|yes| G[lake build -R PvNP Notes]
  F -->|no| H[skip formal build]
```

Optional toy checks can be executed with:

```bash
python3 scripts/verify_notebook.py --checks path/to/toy_checks.py
```

## Research artifact flow

```mermaid
flowchart TD
  A[docs/open_questions.md] --> B[Pick 1 item]
  B --> C[Artifact: Proof / Counterexample / Exact citation / Toy / Barrier]
  C --> D[Update docs/open_questions.md]
  C --> E[Update docs/agent_brief.md]
  C --> F{Proof?}
  F -->|yes| G[formal/PvNP/*.lean\nreal Lean code]
  F -->|no| H[docs/* or formal/Notes/*]
  G --> I[scripts/verify_all.sh]
  H --> I
```

## Resources and search flow

```mermaid
flowchart TD
  A[resources/manifest.tsv] --> B[resources/download_resources.py]
  B --> C[resources/downloads/*]
  C --> D[resources/extract_text_cache.py]
  D --> E[resources/text_cache/*]
  F[resources/downloads/arxiv-metadata-oai-snapshot.json] --> G[scripts/arxiv_search.py]
  G --> H[resources/arxiv/*.tsv]
```

## Formal layer structure

- `formal/PvNP/Main.lean` — entry point for core proofs.
- `formal/PvNP/Work.lean` — WIP proof file and placeholders for active tasks.
- `formal/Notes.lean` — imports all note modules.
- `formal/Notes/*.lean` — long research notes (doc-comments, not proof terms).
- `Paperproof` — external dependency defined in `formal/lakefile.lean`.

## Key control points (where to improve)

- `AGENTS.md`: tighten/relax constraints, artifacts, and anti-loop policy.
- `scripts/agent_prompt.txt`: single-line prompt, easiest high-leverage change.
- `docs/open_questions.md`: quality of StepID + Success criteria determines progress.
- `formal/PvNP/Work.lean`: current proof surface for new Lean facts.
- `scripts/verify_notebook.py`: structural invariants for stability.

## Operating assumptions

- Lean build is optional but preferred; `verify_all.sh` skips if `lake` is missing.
- Docs are short and curated; long reasoning goes into `formal/Notes/`.
- Only `formal/` proofs are considered authoritative.

## Extension checklist

- Add new research question: edit `docs/open_questions.md` with `LeanTarget`.
- Add new Lean fact: implement in `formal/PvNP/` and import via `formal/PvNP/Main.lean`.
- Add new resource: append to `resources/manifest.tsv`, download to `resources/downloads/`.
- Add new check: implement a small `toy_checks.py` and wire through `--checks`.

## Known hot spots

- Q39 and Q43 are active research items (see `docs/open_questions.md`).
- `formal/PvNP/Work.lean` contains placeholders for current formal targets.

