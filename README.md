# P vs NP — verified-first (Lean-first) research log

This repo is a compact, continuously-verified research log aimed at making real progress on **P vs NP** via small, checkable steps (lemmas, counterexamples, exact citations, toy experiments).

## Quick start

- Index: `P_vs_NP.md`
- Current work queue: `docs/open_questions.md`
- Agent working memory (bounded): `docs/agent_brief.md`
- Run checks (markdown + formal, no Jupyter needed): `scripts/verify_all.sh`
- Run the agents (recommended): `./agent/run_trio.sh`
- Light flow (question setter → worker): `./agent/run_flow.sh`
- Summarize the last run log: `python3 agent/analyze_logs.py`

## Repository layout

- `P_vs_NP.md` — short index/status with pointers into `docs/`.
- `docs/` — main text (kept short; history lives in git).
  - `docs/open_questions.md` — the active research queue; **one run picks exactly one item**.
  - `docs/agent_brief.md` — bounded “working memory” to prevent loops (Do-not-repeat).
  - `docs/assumptions.md` — registry of formal External stubs (ASSUMPTIONs).
  - `docs/research/` — short redirect stubs (backwards‑compat; do not write long content here).
- `formal/` — Lean 4 formalization layer.
  - `formal/PvNP/` — core definitions/lemmas.
  - `formal/Notes/` — long research notes as Lean doc‑comments (Lean-first).
  - `formal/External/` — explicit external stubs (ASSUMPTIONs; tracked in `docs/assumptions.md`).
- `resources/manifest.tsv` + `resources/downloads/` — bibliography + pinned PDFs/HTML (hygiene is checked).
- `resources/text_cache/` — optional extracted text cache for fast `rg` over PDFs (gitignored).
- `agent/` — runnable wrappers around Codex CLI, with per-run logs under `agent/logs/` (gitignored).
- `scripts/verify_all.sh` — project verifier (docs + toy checks + optional formal build).
- `scripts/verify_notebook.py` — markdown/toy checks only (used by `verify_all.sh`).

## Verification

Run:

```bash
scripts/verify_all.sh
```

What it does:
- Executes `code/verify_checks.py` (toy sanity checks).
- Verifies `docs/` references to `resources/downloads/` against `resources/manifest.tsv`.
- Verifies `docs/open_questions.md` structure and `docs/agent_brief.md` boundedness/anti-loop fields.
- Verifies prompts stay **single-line**: `scripts/agent_prompt.txt`, `scripts/skeptic_prompt.txt`, `scripts/supervisor_prompt.txt`.
- If Lean is installed, runs `lake build PvNP External Notes` in `formal/` (skipped otherwise).

## Agent automation (WORKER → SKEPTIC → SUPERVISOR)

The default control loop is:
- **WORKER**: do 1 research step (exactly one artifact: Proof / Counterexample / Exact citation / Toy / Reduction / Barrier).
- **SKEPTIC**: try to break/verify the WORKER step (find missing assumptions / errors / “already known” with a precise citation).
- **SUPERVISOR**: enforce protocol + anti-loop; fix prompts/runner only if there is a systemic loop.

Run it:

```bash
./agent/run_trio.sh
```

Light flow (QUESTION_SETTER → WORKER, optional SKEPTIC):

```bash
./agent/run_flow.sh
SKEPTIC_EVERY=5 ./agent/run_flow.sh
```

Common knobs:

```bash
MAX_ROUNDS=1 ./agent/run_trio.sh
PAUSE_SECONDS=2 ./agent/run_trio.sh
REQUIRE_CLEAN=1 ./agent/run_trio.sh
```

Logs:
- Written to `agent/logs/` (symlink: `agent/logs/latest_trio.log`).
- Summary: `python3 agent/analyze_logs.py`

Prompts (all are **1 line** by design):
- WORKER (self-selects a micro-step): `scripts/agent_prompt.txt`
- QUESTION_SETTER: `scripts/question_prompt.txt`
- WORKER (expects Question Set): `scripts/worker_prompt.txt`
- SKEPTIC: `scripts/skeptic_prompt.txt`
- SUPERVISOR: `scripts/supervisor_prompt.txt`

Runner docs: `agent/README.md`

## Resources workflow

List / download by category:

```bash
python3 resources/download_resources.py --list
python3 resources/download_resources.py --category proof_complexity
```

Build/refresh the local text cache for fast search across PDFs:

```bash
python3 resources/extract_text_cache.py
rg -n "Lemma 4\\.4" resources/text_cache/
```
