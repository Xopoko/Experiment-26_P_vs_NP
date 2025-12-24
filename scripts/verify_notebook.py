from __future__ import annotations

import argparse
import json
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


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Execute all code cells in a .ipynb (no Jupyter required).")
    parser.add_argument(
        "path",
        nargs="?",
        type=Path,
        default=Path("P_vs_NP.ipynb"),
        help="Notebook path (default: P_vs_NP.ipynb)",
    )
    parser.add_argument(
        "--allow-magics",
        action="store_true",
        help="Do not fail on lines starting with ! or % (not recommended).",
    )
    args = parser.parse_args(argv)

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
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
