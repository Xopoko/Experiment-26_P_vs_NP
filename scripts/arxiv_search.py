#!/usr/bin/env python3
"""Stream-search arXiv metadata JSONL snapshot."""
from __future__ import annotations

import argparse
import csv
import json
import random
import re
import shlex
import sys
from pathlib import Path

PRESETS: dict[str, dict[str, object]] = {
    "pvnp": {
        "query": (
            "\"proof complexity\" \"extended frege\" \"bounded depth frege\" "
            "\"tseitin\" \"resolution\" \"switching lemma\" \"interpolation\" "
            "\"bounded arithmetic\" \"algebraic proof\" \"polynomial identity testing\" "
            "\"PIT\" \"IPS\" \"natural proofs\" \"algebrization\" "
            "\"relativization\" \"circuit lower bounds\" \"hardness vs randomness\" "
            "\"derandomization\" \"vp vs vnp\" \"gct\" \"communication complexity\" "
            "\"PCP\" \"frege\""
        ),
        "categories": [
            "cs.CC",
            "cs.DS",
            "cs.LO",
            "cs.IT",
            "cs.DM",
            "math.CO",
            "math.LO",
            "math.IT",
            "math.AC",
        ],
        "mode": "or",
        "min_matches": 1,
        "limit": 500,
        "sort": "score",
        "year_min": 1980,
    }
}


def _parse_year(update_date: str, versions: list[dict[str, str]]) -> int:
    if update_date:
        try:
            return int(update_date[:4])
        except ValueError:
            pass
    for v in reversed(versions or []):
        created = v.get("created", "")
        m = re.search(r"\b(19|20)\d{2}\b", created)
        if m:
            return int(m.group(0))
    return 0


def _parse_terms(*, query: str | None, query_file: Path | None) -> list[str]:
    terms: list[str] = []
    if query:
        terms.extend(shlex.split(query))
    if query_file:
        for raw in query_file.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            terms.extend(shlex.split(line))
    return [t.lower() for t in terms if t.strip()]


def _category_match(cats: list[str], filters: list[str]) -> bool:
    if not filters:
        return True
    for f in filters:
        if f.endswith("*"):
            prefix = f[:-1]
            if any(c.startswith(prefix) for c in cats):
                return True
        else:
            if any(c == f or c.startswith(f + ".") for c in cats):
                return True
    return False


def _score_terms(*, title: str, abstract: str, terms: list[str]) -> tuple[int, int]:
    if not terms:
        return 0, 0
    title_l = title.lower()
    abstract_l = abstract.lower()
    score = 0
    matches = 0
    for term in terms:
        if term in title_l:
            score += 3
            matches += 1
        elif term in abstract_l:
            score += 1
            matches += 1
    return score, matches


def _iter_records(path: Path):
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            raw = line.strip()
            if not raw:
                continue
            try:
                yield json.loads(raw)
            except json.JSONDecodeError:
                continue


def _record_key(*, sort: str, score: int, year: int, arxiv_id: str) -> tuple:
    if sort == "date":
        return (year, score, arxiv_id)
    if sort == "random":
        return (random.random(), arxiv_id)
    return (score, year, arxiv_id)


def _write_tsv(rows: list[dict[str, object]], out: Path | None) -> None:
    fieldnames = [
        "id",
        "title",
        "authors",
        "categories",
        "year",
        "update_date",
        "score",
        "abs_url",
        "pdf_url",
        "abstract",
    ]
    out_f = sys.stdout if out is None else out.open("w", encoding="utf-8", newline="")
    try:
        writer = csv.DictWriter(out_f, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    finally:
        if out is not None:
            out_f.close()


def main() -> int:
    parser = argparse.ArgumentParser(description="Search arXiv metadata JSONL snapshot.")
    parser.add_argument(
        "--data",
        default="resources/downloads/arxiv-metadata-oai-snapshot.json",
        help="Path to JSONL snapshot (default: %(default)s)",
    )
    parser.add_argument("--query", help="Query string (quotes preserved, shlex style)")
    parser.add_argument("--query-file", help="File with one query term/phrase per line")
    parser.add_argument("--category", action="append", default=[], help="Category filter (e.g., cs.CC or cs.*)")
    parser.add_argument("--year-min", type=int, default=0)
    parser.add_argument("--year-max", type=int, default=0)
    parser.add_argument("--mode", choices=["and", "or"], default="or")
    parser.add_argument("--min-matches", type=int, default=1)
    parser.add_argument("--min-score", type=int, default=0)
    parser.add_argument("--limit", type=int, default=200)
    parser.add_argument("--sort", choices=["score", "date", "random"], default="score")
    parser.add_argument("--max-abstract-len", type=int, default=320)
    parser.add_argument("--preset", choices=sorted(PRESETS.keys()))
    parser.add_argument("--out", help="Output TSV path (default: stdout)")
    parser.add_argument("--progress", type=int, default=0, help="Print progress every N records")

    args = parser.parse_args()

    query = args.query
    categories = args.category
    year_min = args.year_min
    year_max = args.year_max
    mode = args.mode
    min_matches = args.min_matches
    limit = args.limit
    sort = args.sort

    if args.preset:
        preset = PRESETS[args.preset]
        query = preset.get("query", query)
        categories = preset.get("categories", categories) or categories
        mode = preset.get("mode", mode)
        min_matches = int(preset.get("min_matches", min_matches))
        limit = int(preset.get("limit", limit))
        sort = str(preset.get("sort", sort))
        year_min = int(preset.get("year_min", year_min))
        year_max = int(preset.get("year_max", year_max))

    terms = _parse_terms(query=query, query_file=Path(args.query_file) if args.query_file else None)

    data_path = Path(args.data)
    if not data_path.exists():
        print(f"Missing data file: {data_path}", file=sys.stderr)
        return 2

    rows: list[dict[str, object]] = []
    heap: list[tuple[tuple, dict[str, object]]] = []

    seen = 0
    for rec in _iter_records(data_path):
        seen += 1
        if args.progress and seen % args.progress == 0:
            print(f".. scanned {seen} records", file=sys.stderr)

        title = (rec.get("title") or "").strip().replace("\n", " ")
        abstract = (rec.get("abstract") or "").strip().replace("\n", " ")
        cats = (rec.get("categories") or "").split()

        if not _category_match(cats, categories):
            continue

        year = _parse_year(rec.get("update_date", ""), rec.get("versions", []))
        if year_min and year < year_min:
            continue
        if year_max and year > year_max:
            continue

        score, matches = _score_terms(title=title, abstract=abstract, terms=terms)
        if terms:
            if mode == "and" and matches < len(terms):
                continue
            if mode == "or" and matches < min_matches:
                continue
        if score < args.min_score:
            continue

        arxiv_id = str(rec.get("id", "")).strip()
        abs_url = f"https://arxiv.org/abs/{arxiv_id}" if arxiv_id else ""
        pdf_url = f"https://arxiv.org/pdf/{arxiv_id}.pdf" if arxiv_id else ""
        abstract_out = abstract
        if args.max_abstract_len and len(abstract_out) > args.max_abstract_len:
            abstract_out = abstract_out[: args.max_abstract_len - 3].rstrip() + "..."

        row = {
            "id": arxiv_id,
            "title": title,
            "authors": (rec.get("authors") or "").strip(),
            "categories": " ".join(cats),
            "year": year or "",
            "update_date": rec.get("update_date", ""),
            "score": score,
            "abs_url": abs_url,
            "pdf_url": pdf_url,
            "abstract": abstract_out,
        }

        key = _record_key(sort=sort, score=score, year=year, arxiv_id=arxiv_id)
        if limit and limit > 0:
            import heapq

            if len(heap) < limit:
                heapq.heappush(heap, (key, row))
            else:
                if key > heap[0][0]:
                    heapq.heapreplace(heap, (key, row))
        else:
            rows.append(row)

    if limit and limit > 0:
        rows = [row for _, row in heap]

    rows.sort(key=lambda r: _record_key(sort=sort, score=int(r["score"]), year=int(r["year"] or 0), arxiv_id=str(r["id"])), reverse=True)

    out_path = Path(args.out) if args.out else None
    _write_tsv(rows, out_path)

    if out_path:
        print(f"Wrote {len(rows)} rows to {out_path}", file=sys.stderr)
    else:
        print(f"Rows: {len(rows)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
