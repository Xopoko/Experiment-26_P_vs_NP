# P vs NP — working notes

- Main index: `P_vs_NP.md`
- Main text: `docs/*.md`
- Research scratchpad: `docs/research/`
- Downloads & bibliography: `resources/manifest.tsv`, `resources/downloads/`

## Verify (no Jupyter)

```bash
python3 scripts/verify_notebook.py
```

This runs:
- executable sanity checks in `code/verify_checks.py`
- consistency checks for `docs/` resource links vs `resources/manifest.tsv` and `resources/downloads/`

## Agent prompt

- Canonical 1-sentence prompt for the infinite agent runner: `scripts/agent_prompt.txt`
- Convenience runner (infinite + logging to `agent/logs/`): `agent/run.sh`
- Duo runner (worker + supervisor, infinite + logging to `agent/logs/`): `agent/run_duo.sh`

## Download resources

```bash
python3 resources/download_resources.py --list
python3 resources/download_resources.py --category proof_complexity
```
