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
graph TD
  A[AGENTS.md<br/>protocol + guardrails]
  B[scripts/agent_prompt.txt<br/>single-line prompt]
  C[agent/run.sh<br/>runner + logs]
  D[agent/codex-run.sh<br/>codex exec wrapper]
  E[agent/logs/*.log<br/>per-run logs]

  F[P_vs_NP.md<br/>index]
  G[docs/*<br/>short theory + queue]
  H[docs/open_questions.md<br/>active queue]
  I[docs/agent_brief.md<br/>bounded memory]

  J[formal/PvNP/*<br/>Lean core]
  K[formal/Notes/*<br/>Lean notes]
  L[formal/lakefile.lean<br/>Paperproof dep]

  M[resources/manifest.tsv<br/>bibliography index]
  N[resources/downloads/*<br/>PDF/HTML store]
  O[resources/text_cache/*<br/>optional cache]
  P[scripts/verify_all.sh<br/>CI gate]
  Q[scripts/verify_notebook.py<br/>structure checks]

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
graph TD
  A[agent/run.sh] --> B{REQUIRE_CLEAN?}
  B -->|yes| C[git clean check]
  B -->|no| D[skip check]
  C --> E[log header + lock]
  D --> E
  E --> F[agent/codex-run.sh<br/>codex exec/resume]
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
graph TD
  A[scripts/verify_all.sh] --> B[scripts/verify_notebook.py]
  B --> C[docs structure checks<br/>open_questions + agent_brief]
  B --> D[resources hygiene<br/>manifest vs downloads]
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
graph TD
  A[docs/open_questions.md] --> B[Pick 1 item]
  B --> C[Artifact: Proof / Counterexample / Exact citation / Toy / Barrier]
  C --> D[Update docs/open_questions.md]
  C --> E[Update docs/agent_brief.md]
  C --> F{Proof?}
  F -->|yes| G[formal/PvNP/*.lean<br/>real Lean code]
  F -->|no| H[docs/* or formal/Notes/*]
  G --> I[scripts/verify_all.sh]
  H --> I
```

## Agent behavior architecture (expected protocol)

This is how the agent is expected to behave given `AGENTS.md` and the current pipeline.

Core inputs:
- `AGENTS.md` (rules, artifacts, anti-loop, barrier checks)
- `docs/agent_brief.md` (do-not-repeat + current bottleneck)
- `docs/open_questions.md` (active queue with `NextStepID` + `LeanTarget`)
- `scripts/agent_prompt.txt` (single-line run prompt)
- `agent/logs/` (optional context for supervisors, not required for every run)

Core outputs per run:
- One artifact (Proof / Counterexample / Exact citation / Toy / Reduction / Barrier).
- Updated `docs/open_questions.md` and `docs/agent_brief.md`.
- Passing `scripts/verify_all.sh`.
- One commit with `StepID` in the message.

```mermaid
graph TD
  A[Start run] --> B[Read AGENTS md]
  B --> C[Read agent brief and open questions]
  C --> D{Select item}
  D -->|ok| E[Pick lens]
  E --> F[Formalize claim and toy test]
  F --> G{Artifact ready}
  G -->|no| H[Mark blocked and stop]
  G -->|yes| I[Barrier checks]
  I --> J[Update open questions and agent brief]
  J --> K{Proof artifact}
  K -->|yes| L[Write Lean code in LeanTarget]
  K -->|no| M[Update docs or Notes]
  L --> N[Run verify all]
  M --> N
  N --> O[Commit with StepID]
```

Protocol highlights:
- Exactly one artifact per run. If no artifact: mark BLOCKED and stop.
- Proof artifacts must add real Lean code in the specified `LeanTarget`.
- Anti-loop: do not repeat `StepID` in `agent_brief` and avoid items in cooldown.
- Barrier checks are mandatory for any research step that touches separation claims.

## Resources and search flow

```mermaid
graph TD
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
