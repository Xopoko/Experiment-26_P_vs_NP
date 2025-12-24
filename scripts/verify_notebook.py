from __future__ import annotations

import argparse
import csv
import json
import runpy
import re
import sys
import traceback
from pathlib import Path


def _iter_code_cells(nb: dict) -> list[tuple[int, str]]:
    cells = nb.get("cells", [])
    out: list[tuple[int, str]] = []
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        if not isinstance(source, str):
            raise TypeError(f"Unexpected cell[{i}].source type: {type(source).__name__}")
        out.append((i, source))
    return out


def _assert_no_magics(cell_index: int, source: str) -> None:
    for raw_line in source.splitlines():
        line = raw_line.lstrip()
        if not line:
            continue
        if line.startswith("!") or line.startswith("%"):
            raise AssertionError(f"cell {cell_index}: contains notebook magic/shell line: {raw_line!r}")


def _load_manifest_ids(path: Path) -> set[str]:
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        required = {"id", "category", "authors", "year", "title", "url", "notes"}
        if set(reader.fieldnames or []) != required:
            raise AssertionError(
                f"Unexpected header in {path}. Expected: {sorted(required)}; got: {reader.fieldnames}"
            )
        ids: set[str] = set()
        for row in reader:
            rid = (row.get("id") or "").strip()
            if not rid:
                raise AssertionError(f"{path}: empty id row")
            if rid in ids:
                raise AssertionError(f"{path}: duplicate id: {rid}")
            ids.add(rid)
        return ids


def _iter_markdown_paths() -> list[Path]:
    paths: list[Path] = []
    for root in [Path("P_vs_NP.md"), Path("docs")]:
        if root.is_file():
            paths.append(root)
        elif root.is_dir():
            paths.extend(sorted(p for p in root.rglob("*.md") if p.is_file()))
    return paths


def _verify_download_links(*, manifest_path: Path, downloads_dir: Path) -> None:
    manifest_ids = _load_manifest_ids(manifest_path)
    md_paths = _iter_markdown_paths()
    rx = re.compile(r"resources/downloads/([A-Za-z0-9._-]+\.(?:pdf|html))")

    missing_files: list[str] = []
    missing_manifest: list[str] = []

    for md_path in md_paths:
        text = md_path.read_text(encoding="utf-8")
        for m in rx.finditer(text):
            filename = m.group(1)
            local_path = downloads_dir / filename
            if not local_path.exists():
                line = text.count("\n", 0, m.start()) + 1
                missing_files.append(f"{md_path}:{line}: {local_path}")
                continue

            rid = Path(filename).stem
            if rid not in manifest_ids:
                line = text.count("\n", 0, m.start()) + 1
                missing_manifest.append(f"{md_path}:{line}: id {rid} (from {filename}) not in {manifest_path}")

    if missing_files or missing_manifest:
        msg = ["Resource link verification failed:"]
        if missing_files:
            msg.append("Missing downloads:")
            msg.extend(f"- {x}" for x in missing_files)
        if missing_manifest:
            msg.append("Missing manifest entries:")
            msg.extend(f"- {x}" for x in missing_manifest)
        raise AssertionError("\n".join(msg))

    print(f"OK: verified {len(md_paths)} markdown files resource links against {manifest_path}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Run project checks from a .py file or execute code cells from a legacy .ipynb (no Jupyter required)."
    )
    parser.add_argument(
        "path",
        nargs="?",
        type=Path,
        default=Path("code/verify_checks.py"),
        help="Path to a .py checks file or a legacy .ipynb (default: code/verify_checks.py)",
    )
    parser.add_argument(
        "--allow-magics",
        action="store_true",
        help="Do not fail on lines starting with ! or % (not recommended).",
    )
    parser.add_argument(
        "--skip-resource-checks",
        action="store_true",
        help="Skip verifying docs/ resource links vs resources/manifest.tsv and resources/downloads/.",
    )
    args = parser.parse_args(argv)

    if args.path.suffix == ".py":
        try:
            runpy.run_path(str(args.path), run_name="__main__")
        except Exception as exc:  # noqa: BLE001 - show full context
            print(f"FAILED: {args.path}: {exc}", file=sys.stderr)
            traceback.print_exc()
            return 1
        print(f"OK: executed {args.path}")
        if not args.skip_resource_checks:
            _verify_download_links(
                manifest_path=Path("resources/manifest.tsv"),
                downloads_dir=Path("resources/downloads"),
            )
        return 0

    if args.path.suffix != ".ipynb":
        print(f"FAILED: {args.path}: expected .py or .ipynb", file=sys.stderr)
        return 2

    nb = json.loads(args.path.read_text(encoding="utf-8"))
    code_cells = _iter_code_cells(nb)

    env: dict[str, object] = {"__name__": "__main__"}
    for cell_index, source in code_cells:
        if not args.allow_magics:
            _assert_no_magics(cell_index, source)
        filename = f"{args.path}#cell_{cell_index}"
        try:
            code = compile(source, filename, "exec", dont_inherit=True)
            exec(code, env)  # noqa: S102 - deliberate: verification harness
        except Exception as exc:  # noqa: BLE001 - show full context
            print(f"FAILED: {filename}: {exc}", file=sys.stderr)
            traceback.print_exc()
            return 1

    print(f"OK: executed {len(code_cells)} code cells from {args.path}")
    if not args.skip_resource_checks:
        _verify_download_links(
            manifest_path=Path("resources/manifest.tsv"),
            downloads_dir=Path("resources/downloads"),
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
