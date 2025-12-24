# Resources

- Manifest: `resources/manifest.tsv`
- List: `python3 resources/download_resources.py --list`
- Download PDFs for a category: `python3 resources/download_resources.py --category circuits`
- Proof complexity PDFs: `python3 resources/download_resources.py --category proof_complexity`
- PCP PDFs: `python3 resources/download_resources.py --category pcp`
- Download one item: `python3 resources/download_resources.py --id hastad_1986`
- The downloader validates PDF magic bytes; paywalled/HTML responses are saved as `.html` and reported as `FAIL`.
- If a host has broken TLS certs: add `--insecure`
