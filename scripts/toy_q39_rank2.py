#!/usr/bin/env python3
"""Toy check: contiguous alt-shift rank-2 witness for Q39."""
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import Dict, List, Tuple

_ALT_RE = re.compile(
    r"def\s+Q39_globalfixedpair_fixedorientation_contiguous_shift_alt(\d+)_vec([12])"
    r"\s*:\s*BitVec12\s*:=\s*\[(.*?)\]",
    re.S,
)


def _parse_bool_list(raw: str) -> List[int]:
    items = [item.strip() for item in raw.replace("\n", " ").split(",") if item.strip()]
    vals: List[int] = []
    for item in items:
        if item == "true":
            vals.append(1)
        elif item == "false":
            vals.append(0)
        else:
            raise ValueError(f"unexpected literal {item!r} in vector list")
    return vals


def _load_alt_vectors(path: Path) -> Dict[int, Dict[int, List[int]]]:
    text = path.read_text(encoding="utf-8")
    alts: Dict[int, Dict[int, List[int]]] = {}
    for match in _ALT_RE.finditer(text):
        alt = int(match.group(1))
        vec_idx = int(match.group(2))
        vec = _parse_bool_list(match.group(3))
        alts.setdefault(alt, {})[vec_idx] = vec
    return alts


def _shift_left(vec: List[int]) -> List[int]:
    if not vec:
        return vec
    return vec[1:] + vec[:1]


def _shift_right(vec: List[int]) -> List[int]:
    if not vec:
        return vec
    return vec[-1:] + vec[:-1]


def _detect_shift_direction(alts: Dict[int, Dict[int, List[int]]]) -> str:
    for alt in sorted(alts, reverse=True):
        if alt + 1 not in alts:
            continue
        v1 = alts[alt].get(1)
        v2 = alts[alt].get(2)
        n1 = alts[alt + 1].get(1)
        n2 = alts[alt + 1].get(2)
        if v1 is None or v2 is None or n1 is None or n2 is None:
            continue
        if _shift_left(v1) == n1 and _shift_left(v2) == n2:
            return "left"
        if _shift_right(v1) == n1 and _shift_right(v2) == n2:
            return "right"
    raise ValueError("unable to infer shift direction from consecutive alt definitions")


def _rank_two(vec1: List[int], vec2: List[int]) -> int:
    zero1 = all(bit == 0 for bit in vec1)
    zero2 = all(bit == 0 for bit in vec2)
    if zero1 and zero2:
        return 0
    if zero1 or zero2:
        return 1
    if vec1 == vec2:
        return 1
    return 2


def _format_vec(vec: List[int]) -> str:
    return "".join(str(bit) for bit in vec)


def _indices(vec: List[int]) -> List[int]:
    return [i for i, bit in enumerate(vec) if bit]


def _get_alt_vectors(
    alts: Dict[int, Dict[int, List[int]]], alt: int, direction: str
) -> Tuple[List[int], List[int], str]:
    if alt in alts and 1 in alts[alt] and 2 in alts[alt]:
        return alts[alt][1], alts[alt][2], "from-file"

    if not alts:
        raise ValueError("no alt vectors found in Lean file")
    max_alt = max(alts)
    if alt <= max_alt:
        raise ValueError(f"alt{alt} missing; known max alt is {max_alt}")

    step = _shift_left if direction == "left" else _shift_right
    vec1 = alts[max_alt][1]
    vec2 = alts[max_alt][2]
    for _ in range(alt - max_alt):
        vec1 = step(vec1)
        vec2 = step(vec2)
    return vec1, vec2, f"shifted-from-alt{max_alt}"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Toy check for Q39 contiguous alt-shift rank-2 witness."
    )
    parser.add_argument("--alt", type=int, default=54, help="Alt shift number (e.g. 54).")
    parser.add_argument(
        "--lean",
        type=Path,
        default=Path("formal/WIP/Work.lean"),
        help="Path to the Lean file with Q39 alt vectors.",
    )
    args = parser.parse_args()

    alts = _load_alt_vectors(args.lean)
    direction = _detect_shift_direction(alts)
    vec1, vec2, source = _get_alt_vectors(alts, args.alt, direction)

    if len(vec1) != len(vec2):
        raise SystemExit("vector length mismatch")

    rank = _rank_two(vec1, vec2)
    print("Toy check: Q39 contiguous alt-shift rank-2 witness")
    print(f"alt={args.alt} source={source} shift={direction} length={len(vec1)}")
    print(f"vec1={_format_vec(vec1)} ones={_indices(vec1)}")
    print(f"vec2={_format_vec(vec2)} ones={_indices(vec2)}")
    print(f"rank={rank}")

    if rank != 2:
        raise SystemExit(f"rank check failed: expected 2, got {rank}")


if __name__ == "__main__":
    main()
