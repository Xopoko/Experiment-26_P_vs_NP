# arXiv metadata

Source: `resources/downloads/arxiv-metadata-oai-snapshot.json` (JSONL, one record per line).
This file is not committed; download a local snapshot and place it at the path above.

Search:
- `python3 scripts/arxiv_search.py --query '"proof complexity" "tseitin"' --category cs.CC --limit 50`
- `python3 scripts/arxiv_search.py --preset pvnp --out resources/arxiv/pvnp_slice.tsv`

Notes:
- The search script streams the JSONL file; no index is built.
- Output is TSV with URLs for `abs` and `pdf`.
