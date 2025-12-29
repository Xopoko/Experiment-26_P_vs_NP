# Agent runner

Run the single worker loop (self-selects a micro-step and commits):

```bash
./agent/run.sh
REQUIRE_CLEAN=1 ./agent/run.sh
./agent/run_wip.sh   # RUN_MODE=wip, LEAN_FORCE_REBUILD=0
./agent/run_core.sh  # RUN_MODE=core, LEAN_FORCE_REBUILD=1
```

Logs are written to `agent/logs/` (symlink: `agent/logs/latest.log`).
