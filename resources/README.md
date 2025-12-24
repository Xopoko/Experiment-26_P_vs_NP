# Resources

- Manifest: `resources/manifest.tsv`
- List: `python3 resources/download_resources.py --list`
- `--list` includes a `local` column (`pdf`/`html`/`—`) for what’s already in `resources/downloads/`
- Download PDFs for a category: `python3 resources/download_resources.py --category circuits`
- Proof complexity PDFs: `python3 resources/download_resources.py --category proof_complexity`
- Bounded arithmetic PDFs: `python3 resources/download_resources.py --category bounded_arithmetic`
- PCP PDFs: `python3 resources/download_resources.py --category pcp`
- Download one item: `python3 resources/download_resources.py --id hastad_1986`
- The downloader validates PDF magic bytes; paywalled/HTML responses are saved as `.html` and reported as `FAIL`.
- Some publisher/DOI links may be blocked (403); see `notes` in `resources/manifest.tsv` for alternatives.
- If a host has broken TLS certs: add `--insecure`
- If you get `CERTIFICATE_VERIFY_FAILED` in a minimal environment, install CA certs (preferred) or use `--insecure`.
- Verify notebook code-cells (no Jupyter): `python3 scripts/verify_notebook.py P_vs_NP.ipynb`
