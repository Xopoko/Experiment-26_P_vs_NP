# Agent runner

Run the single worker loop (self-selects a micro-step and commits):

```bash
./agent/run.sh
REQUIRE_CLEAN=1 ./agent/run.sh
```

Logs are written to `agent/logs/` (symlink: `agent/logs/latest.log`).
