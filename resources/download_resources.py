from __future__ import annotations

import argparse
import csv
import re
import ssl
import sys
import urllib.request
from urllib.parse import urlparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Resource:
    id: str
    category: str
    authors: str
    year: str
    title: str
    url: str
    notes: str

    @property
    def is_pdf(self) -> bool:
        url = self.url.lower()
        if ".pdf" in url:
            return True
        parsed = urlparse(url)
        path = parsed.path
        if "/pdf/" in path or path.endswith("/pdf"):
            return True

        # Some repositories serve PDFs behind a stable `/download` endpoint without a `.pdf` suffix.
        if parsed.netloc.endswith("eccc.weizmann.ac.il") and path.rstrip("/").endswith("/download"):
            return True

        return False


def _read_manifest(path: Path) -> list[Resource]:
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        required = {"id", "category", "authors", "year", "title", "url", "notes"}
        if set(reader.fieldnames or []) != required:
            raise ValueError(
                f"Unexpected header in {path}. Expected: {sorted(required)}; got: {reader.fieldnames}"
            )
        out: list[Resource] = []
        for row in reader:
            out.append(
                Resource(
                    id=row["id"].strip(),
                    category=row["category"].strip(),
                    authors=row["authors"].strip(),
                    year=row["year"].strip(),
                    title=row["title"].strip(),
                    url=row["url"].strip(),
                    notes=row["notes"].strip(),
                )
            )
        return out


def _safe_filename(name: str) -> str:
    name = name.strip().lower()
    name = re.sub(r"[^a-z0-9._-]+", "_", name)
    name = re.sub(r"_+", "_", name).strip("_")
    return name or "download"


def _download(
    url: str,
    out_path: Path,
    *,
    user_agent: str,
    timeout_sec: float,
    verify_tls: bool,
) -> None:
    req = urllib.request.Request(url, headers={"User-Agent": user_agent})
    context = None
    if url.lower().startswith("https://"):
        if verify_tls:
            context = ssl.create_default_context()
        else:
            context = ssl._create_unverified_context()  # noqa: SLF001 - CLI option

    with urllib.request.urlopen(req, timeout=timeout_sec, context=context) as resp:
        out_path.write_bytes(resp.read())


def _looks_like_pdf(path: Path) -> bool:
    try:
        with path.open("rb") as f:
            head = f.read(1024)
    except OSError:
        return False
    return b"%PDF-" in head


def _rename_overwrite(src: Path, dst: Path) -> None:
    if dst.exists():
        dst.unlink()
    src.rename(dst)


def _print_table(resources: Iterable[Resource]) -> None:
    rows = list(resources)
    if not rows:
        return

    cols = [
        ("id", max(len("id"), *(len(r.id) for r in rows))),
        ("category", max(len("category"), *(len(r.category) for r in rows))),
        ("year", max(len("year"), *(len(r.year) for r in rows))),
        ("title", max(len("title"), *(min(len(r.title), 60) for r in rows))),
        ("kind", len("kind")),
    ]

    def trunc(s: str, n: int) -> str:
        return s if len(s) <= n else (s[: n - 1] + "…")

    header = "  ".join(name.ljust(width) for name, width in cols)
    print(header)
    print("-" * len(header))
    for r in rows:
        values = [
            r.id,
            r.category,
            r.year,
            trunc(r.title, 60),
            ("pdf" if r.is_pdf else "link"),
        ]
        print("  ".join(v.ljust(width) for v, (_, width) in zip(values, cols, strict=True)))


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Download literature links listed in resources/manifest.tsv",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path(__file__).with_name("manifest.tsv"),
        help="Path to manifest.tsv (default: resources/manifest.tsv)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("downloads"),
        help="Output directory for downloads (default: resources/downloads/)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List known resources and exit",
    )
    parser.add_argument(
        "--category",
        action="append",
        default=[],
        help="Filter by category (repeatable)",
    )
    parser.add_argument(
        "--id",
        dest="ids",
        action="append",
        default=[],
        help="Download only this id (repeatable)",
    )
    parser.add_argument(
        "--include-non-pdf",
        action="store_true",
        help="Allow downloading non-PDF links (HTML, DOI pages, etc.)",
    )
    parser.add_argument(
        "--insecure",
        action="store_true",
        help="Disable TLS certificate verification (use only if a host has broken certs).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Per-request timeout in seconds (default: 60).",
    )
    parser.add_argument(
        "--user-agent",
        default="Mozilla/5.0 (Codex CLI; +https://openai.com)",
        help="HTTP User-Agent header",
    )

    args = parser.parse_args(argv)

    resources = _read_manifest(args.manifest)
    if args.list:
        _print_table(resources)
        return 0

    selected = resources
    if args.category:
        cats = set(args.category)
        selected = [r for r in selected if r.category in cats]
    if args.ids:
        want = set(args.ids)
        selected = [r for r in selected if r.id in want]

    if not selected:
        print("No resources matched filters.", file=sys.stderr)
        return 2

    args.out.mkdir(parents=True, exist_ok=True)
    failures = 0
    for r in selected:
        if not args.include_non_pdf and not r.is_pdf:
            print(f"SKIP {r.id}: not a direct PDF link ({r.url})")
            continue

        ext = ".pdf" if r.is_pdf else ".html"
        out_path = args.out / f"{_safe_filename(r.id)}{ext}"
        try:
            _download(
                r.url,
                out_path,
                user_agent=args.user_agent,
                timeout_sec=args.timeout,
                verify_tls=not args.insecure,
            )
            expected_pdf = r.is_pdf
            actual_pdf = _looks_like_pdf(out_path)

            if expected_pdf and not actual_pdf:
                failures += 1
                html_path = out_path.with_suffix(".html")
                _rename_overwrite(out_path, html_path)
                print(
                    f"FAIL {r.id}: expected PDF but got non-PDF content -> {html_path}",
                    file=sys.stderr,
                )
                continue

            if (not expected_pdf) and actual_pdf:
                pdf_path = out_path.with_suffix(".pdf")
                _rename_overwrite(out_path, pdf_path)
                out_path = pdf_path
                print(f"OK   {r.id} -> {out_path} (detected PDF)")
                continue

            print(f"OK   {r.id} -> {out_path}")
        except Exception as e:  # noqa: BLE001 - CLI: show all failures
            failures += 1
            print(f"FAIL {r.id}: {e}", file=sys.stderr)

    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
