from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def _extract_one(*, pdf_path: Path, out_txt: Path, layout: bool) -> None:
    out_txt.parent.mkdir(parents=True, exist_ok=True)

    pdftotext = shutil.which("pdftotext")
    if not pdftotext:
        raise RuntimeError("pdftotext not found in PATH (install poppler-utils)")

    tmp_path = out_txt.with_suffix(out_txt.suffix + ".tmp")
    if tmp_path.exists():
        tmp_path.unlink()

    cmd = [pdftotext, "-enc", "UTF-8"]
    if layout:
        cmd.append("-layout")
    cmd.extend([str(pdf_path), str(tmp_path)])
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)

    tmp_path.replace(out_txt)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Build a local, gitignored text cache for PDFs in resources/downloads/ (for fast rg/search).",
    )
    parser.add_argument(
        "--downloads",
        type=Path,
        default=Path(__file__).with_name("downloads"),
        help="Directory with downloaded PDFs (default: resources/downloads/)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).with_name("text_cache"),
        help="Output directory for extracted text (default: resources/text_cache/)",
    )
    parser.add_argument(
        "--id",
        dest="ids",
        action="append",
        default=[],
        help="Only extract for this id (stem of the PDF filename, repeatable).",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Re-extract even if the .txt is newer than the .pdf.",
    )
    parser.add_argument(
        "--layout",
        action="store_true",
        help="Use pdftotext -layout (often better for tables, sometimes worse for search).",
    )
    args = parser.parse_args(argv)

    if not args.downloads.exists():
        print(f"Missing downloads dir: {args.downloads}", file=sys.stderr)
        return 2

    want = set(args.ids)
    pdfs = sorted(p for p in args.downloads.glob("*.pdf") if p.is_file())
    if want:
        pdfs = [p for p in pdfs if p.stem in want]

    if not pdfs:
        print("No PDFs matched.", file=sys.stderr)
        return 2

    failures = 0
    extracted = 0
    skipped = 0

    for pdf_path in pdfs:
        out_txt = args.out / f"{pdf_path.stem}.txt"

        if not args.force and out_txt.exists():
            try:
                if out_txt.stat().st_mtime >= pdf_path.stat().st_mtime:
                    skipped += 1
                    continue
            except OSError:
                pass

        try:
            _extract_one(pdf_path=pdf_path, out_txt=out_txt, layout=args.layout)
            extracted += 1
        except subprocess.CalledProcessError as exc:
            failures += 1
            err = (exc.stderr or "").strip()
            print(f"FAIL {pdf_path.name}: pdftotext exited {exc.returncode}: {err}", file=sys.stderr)
        except Exception as exc:  # noqa: BLE001 - CLI utility
            failures += 1
            print(f"FAIL {pdf_path.name}: {exc}", file=sys.stderr)

    print(f"OK: extracted={extracted}, skipped={skipped}, failures={failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

