# Agent runners

## Worker (single agent)

Run forever, reuse the canonical prompt, write logs to `agent/logs/`:

```bash
./agent/run.sh
```

## Duo (worker + supervisor)

Run forever: each round does WORKER (research step) → SUPERVISOR (review/policy fixes).
Logs go to `agent/logs/latest_duo.log`.

```bash
./agent/run_duo.sh
```

Optional controls:

```bash
MAX_ROUNDS=3 ./agent/run_duo.sh
PAUSE_SECONDS=2 ./agent/run_duo.sh
```

Notes:
- Don’t pass `--infinite` to `run_duo.sh` (it already loops).
- Prompts: `scripts/agent_prompt.txt` (worker) and `scripts/supervisor_prompt.txt` (supervisor).
