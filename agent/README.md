# Agent runners

## Worker (single agent)

Run forever with the standalone WORKER prompt (self-selects a micro-step), write logs to `agent/logs/`:

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
REQUIRE_CLEAN=1 ./agent/run_duo.sh
```

Notes:
- Don’t pass `--infinite` to `run_duo.sh` (it already loops).
- Prompts: `scripts/agent_prompt.txt` (worker, self-select) and `scripts/supervisor_prompt.txt` (supervisor).
- Both runners take a lock (default: `agent/logs/.agent.lock`) to prevent concurrent runs; override via `LOCK_FILE=...`.

## Trio (worker + skeptic + supervisor)

Run forever: each round does WORKER (research step) → SKEPTIC (try to break/check novelty) → SUPERVISOR (policy/anti-loop fixes).
Logs go to `agent/logs/latest_trio.log`.

```bash
./agent/run_trio.sh
```

Optional controls:

```bash
MAX_ROUNDS=3 ./agent/run_trio.sh
PAUSE_SECONDS=2 ./agent/run_trio.sh
REQUIRE_CLEAN=1 ./agent/run_trio.sh
```

Notes:
- Don’t pass `--infinite` to `run_trio.sh` (it already loops).
- Prompts: `scripts/agent_prompt.txt` (worker, self-select), `scripts/skeptic_prompt.txt` (skeptic), `scripts/supervisor_prompt.txt` (supervisor).
- Uses the same lock mechanism as the other runners.

## Flow (question setter → worker; optional skeptic)

This is a lighter loop close to “decompose → solve”:
QUESTION_SETTER prepares a single “Question Set”, then WORKER executes exactly one micro-step.

```bash
./agent/run_flow.sh
```

Optional knobs:

```bash
SKEPTIC_EVERY=5 ./agent/run_flow.sh   # run skeptic every 5th round
MAX_ROUNDS=1 ./agent/run_flow.sh
REQUIRE_CLEAN=1 ./agent/run_flow.sh
```

Notes:
- Logs go to `agent/logs/latest_flow.log`.
- Prompts: `scripts/question_prompt.txt` (question setter) and `scripts/worker_prompt.txt` (worker expecting the Question Set) (+ `scripts/skeptic_prompt.txt` if enabled).

## Log maintenance

Keep only the newest 50 log files:

```bash
./agent/prune_logs.sh --keep 50
```

Or delete logs older than 14 days (then enforce keep):

```bash
./agent/prune_logs.sh --days 14 --keep 200
```

## Log analysis (quick triage)

Summarize the latest run log (prefers trio → duo → single):

```bash
python3 agent/analyze_logs.py
```

Or pick a specific mode / file:

```bash
python3 agent/analyze_logs.py --mode trio
python3 agent/analyze_logs.py --log agent/logs/latest_duo.log
python3 agent/analyze_logs.py --log agent/logs/20251225T183643Z_pid1882214.duo.log
```
