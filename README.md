# P vs NP — verified-first (Lean-first) research log

This repo is a compact, continuously-verified research log aimed at making real progress on **P vs NP** via small, checkable steps (lemmas, counterexamples, exact citations, toy experiments).

## Quick start

- Index: `P_vs_NP.md`
- Current work queue: `docs/open_questions.md`
- Agent working memory (bounded): `docs/agent_brief.md`
- Run checks (markdown + formal, no Jupyter needed): `scripts/verify_all.sh`
- Run the agent: `./agent/run.sh`

## Repository layout

- `P_vs_NP.md` — short index/status with pointers into `docs/`.
- `docs/` — main text (kept short; history lives in git).
  - `docs/open_questions.md` — the active research queue; **one run picks exactly one item**.
  - `docs/agent_brief.md` — bounded “working memory” to prevent loops (Do-not-repeat).
- `formal/` — Lean 4 formalization layer.
  - `formal/PvNP/` — core definitions/lemmas.
  - `formal/Notes/` — long research notes as Lean doc‑comments (Lean-first).
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
- Verifies `docs/` references to `resources/downloads/` against `resources/manifest.tsv`.
- Verifies `docs/open_questions.md` structure and `docs/agent_brief.md` boundedness/anti-loop fields.
- Verifies prompt stays **single-line**: `scripts/agent_prompt.txt`.
- If Lean is installed, runs `lake build PvNP Notes` in `formal/` (skipped otherwise).

Optional toy checks:

```bash
python3 scripts/verify_notebook.py --checks path/to/toy_checks.py
```

## Agent automation (single WORKER loop)

Run it:

```bash
./agent/run.sh
REQUIRE_CLEAN=1 ./agent/run.sh
```

Logs:
- Written to `agent/logs/` (symlink: `agent/logs/latest.log`).

Prompt (single-line):
- `scripts/agent_prompt.txt`

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
