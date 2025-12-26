from __future__ import annotations

import argparse
import csv
import json
import runpy
import re
import subprocess
import sys
import traceback
from pathlib import Path


_STEP_ID_RE = re.compile(r"^Q\d{1,4}\.S\d{1,4}(?:-[a-z0-9][a-z0-9-]*)?$")


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


def _find_markdown_section(lines: list[str], *, header: str) -> tuple[int, int]:
    start = None
    for i, line in enumerate(lines):
        if line.strip() == header:
            start = i + 1
            break
    if start is None:
        raise AssertionError(f"Missing section header: {header!r}")

    end = len(lines)
    for j in range(start, len(lines)):
        if lines[j].startswith("## ") and lines[j].strip() != header:
            end = j
            break
    return start, end


def _parse_step_id(value: str, *, context: str) -> str:
    token = value.strip().split()[0] if value.strip() else ""
    if not token:
        raise AssertionError(f"{context}: missing StepID value")
    if not _STEP_ID_RE.match(token):
        raise AssertionError(f"{context}: invalid StepID {token!r} (expected Qxx.Sy.slug)")
    return token


def _parse_infogain(value: str, *, context: str) -> int:
    raw = value.strip().split()[0] if value.strip() else ""
    if raw not in {"0", "1", "2"}:
        raise AssertionError(f"{context}: invalid InfoGain {raw!r} (expected 0/1/2)")
    return int(raw)


def _extract_backticked_meta(lines: list[str], *, key: str) -> str | None:
    needle = f"`{key}:`"
    for line in lines:
        if needle not in line:
            continue
        return line.split(needle, 1)[1].strip()
    return None


def _verify_open_questions_structure(*, path: Path) -> None:
    if not path.exists():
        raise AssertionError(f"Missing required file: {path}")

    raw = path.read_text(encoding="utf-8")
    lines = raw.splitlines()
    start, end = _find_markdown_section(lines, header="## Активные")
    section = lines[start:end]

    items: list[list[str]] = []
    current: list[str] = []
    for line in section:
        if line.startswith("- [ ]"):
            if current:
                items.append(current)
            current = [line]
            continue
        if current:
            current.append(line)
    if current:
        items.append(current)

    if not items:
        raise AssertionError(f"{path}: no active items found under '## Активные'")

    seen_ids: set[str] = set()
    for item in items:
        head = item[0]
        m = re.search(r"\*\*(Q\d{1,4})\b", head)
        qid = m.group(1) if m else head.strip()
        if qid in seen_ids:
            raise AssertionError(f"{path}: duplicate active id: {qid}")
        seen_ids.add(qid)

        priority = _extract_backticked_meta(item, key="Priority")
        if priority is None:
            raise AssertionError(f"{path}: {qid}: missing `Priority:`")
        pr = priority.strip().split()[0]
        if pr not in {"P0", "P1", "P2"}:
            raise AssertionError(f"{path}: {qid}: invalid Priority {pr!r} (expected P0/P1/P2)")

        status = _extract_backticked_meta(item, key="Status")
        if status is None:
            raise AssertionError(f"{path}: {qid}: missing `Status:`")
        st = status.strip().split()[0].upper()
        if st not in {"ACTIVE", "BLOCKED", "DONE"}:
            raise AssertionError(f"{path}: {qid}: invalid Status {st!r} (expected ACTIVE/BLOCKED/DONE)")

        next_step = _extract_backticked_meta(item, key="NextStepID")
        if next_step is None:
            raise AssertionError(f"{path}: {qid}: missing `NextStepID:`")
        _parse_step_id(next_step, context=f"{path}: {qid}: NextStepID")

        success = _extract_backticked_meta(item, key="Success")
        if success is None:
            raise AssertionError(f"{path}: {qid}: missing `Success:`")
        if not success.strip():
            raise AssertionError(f"{path}: {qid}: empty `Success:`")

        last_step = _extract_backticked_meta(item, key="LastStepID")
        if last_step is not None and last_step.strip():
            _parse_step_id(last_step, context=f"{path}: {qid}: LastStepID")

    print(f"OK: verified open questions structure in {path}")


def _verify_agent_brief_structure(*, path: Path) -> None:
    if not path.exists():
        raise AssertionError(f"Missing required file: {path}")

    raw = path.read_text(encoding="utf-8")
    lines = raw.splitlines()
    start, end = _find_markdown_section(lines, header="## Anti-loop (обновлять, не раздувать)")
    section = lines[start:end]

    last_step = _extract_backticked_meta(section, key="LastStepID")
    if last_step is None:
        raise AssertionError(f"{path}: missing `LastStepID:` in Anti-loop section")
    _parse_step_id(last_step, context=f"{path}: Anti-loop: LastStepID")

    dont_repeat = _extract_backticked_meta(section, key="Do-not-repeat (next 2 runs)")
    if dont_repeat is None:
        raise AssertionError(f"{path}: missing `Do-not-repeat (next 2 runs):` in Anti-loop section")
    step_ids = [s.strip() for s in dont_repeat.split(",") if s.strip()]
    if not step_ids:
        raise AssertionError(f"{path}: Anti-loop: empty Do-not-repeat list")
    for sid in step_ids:
        _parse_step_id(sid, context=f"{path}: Anti-loop: Do-not-repeat")

    last_infogain = _extract_backticked_meta(section, key="Last InfoGain")
    if last_infogain is None:
        raise AssertionError(f"{path}: missing `Last InfoGain:` in Anti-loop section")
    _parse_infogain(last_infogain, context=f"{path}: Anti-loop: Last InfoGain")

    print(f"OK: verified agent brief Anti-loop structure in {path}")


def _verify_agent_brief(*, path: Path, max_lines: int, max_bytes: int, max_experiments: int) -> None:
    if not path.exists():
        raise AssertionError(f"Missing required file: {path}")

    raw = path.read_text(encoding="utf-8")
    if len(raw.encode("utf-8")) > max_bytes:
        raise AssertionError(f"{path} is too large: > {max_bytes} bytes (compress it, do not append)")

    lines = raw.splitlines()
    if len(lines) > max_lines:
        raise AssertionError(f"{path} is too long: {len(lines)} lines > {max_lines} (compress it, do not append)")

    experiments = [ln for ln in lines if ln.lstrip().startswith("- E")]
    if len(experiments) > max_experiments:
        raise AssertionError(
            f"{path} has too many experiment entries: {len(experiments)} > {max_experiments} (compress/overwrite)"
        )

    print(f"OK: verified bounded agent brief: {path}")


def _verify_prompt_files(*, paths: list[Path], max_bytes: int = 4096) -> None:
    for path in paths:
        if not path.exists():
            raise AssertionError(f"Missing required file: {path}")

        raw = path.read_text(encoding="utf-8")
        if len(raw.encode("utf-8")) > max_bytes:
            raise AssertionError(f"{path} is too large: > {max_bytes} bytes (keep prompts 1 sentence)")

        lines = raw.splitlines()
        if len(lines) != 1:
            raise AssertionError(f"{path} must be exactly 1 line (one sentence prompt), got {len(lines)} lines")
        if not lines[0].strip():
            raise AssertionError(f"{path} is empty")

    print(f"OK: verified single-line prompts: {', '.join(str(p) for p in paths)}")


def _verify_assumptions_registry(*, path: Path) -> None:
    if not path.exists():
        raise AssertionError(f"{path} missing (required by AGENTS.md)")
    text = path.read_text(encoding="utf-8")
    if "Assumption registry" not in text:
        raise AssertionError(f"{path} missing header 'Assumption registry'")
    if "Total stubs" not in text:
        raise AssertionError(f"{path} missing 'Total stubs' summary")


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


def _verify_download_dir_hygiene(*, manifest_path: Path, downloads_dir: Path) -> None:
    manifest_ids = _load_manifest_ids(manifest_path)

    stray_files: list[str] = []
    for p in sorted(downloads_dir.iterdir()):
        if not p.is_file():
            continue
        if p.suffix.lower() not in {".pdf", ".html"}:
            continue
        if p.stem not in manifest_ids:
            stray_files.append(str(p))

    untracked: list[str] = []
    try:
        res = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard", "--", str(downloads_dir)],
            check=False,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError:
        res = None

    if res and res.returncode == 0:
        for raw in res.stdout.splitlines():
            rel = raw.strip()
            if not rel:
                continue
            path = Path(rel)
            if path.suffix.lower() in {".pdf", ".html"}:
                untracked.append(rel)

    if stray_files or untracked:
        msg = ["Download directory hygiene check failed:"]
        if stray_files:
            msg.append(f"Files in {downloads_dir} missing from {manifest_path}:")
            msg.extend(f"- {x}" for x in stray_files)
        if untracked:
            msg.append(f"Untracked files in {downloads_dir} (add to git or remove):")
            msg.extend(f"- {x}" for x in untracked)
        raise AssertionError("\n".join(msg))

    print(f"OK: verified downloads hygiene in {downloads_dir}")


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
            _verify_download_dir_hygiene(
                manifest_path=Path("resources/manifest.tsv"),
                downloads_dir=Path("resources/downloads"),
            )
            _verify_agent_brief(
                path=Path("docs/agent_brief.md"),
                max_lines=200,
                max_bytes=16_000,
                max_experiments=12,
            )
            _verify_agent_brief_structure(path=Path("docs/agent_brief.md"))
            _verify_open_questions_structure(path=Path("docs/open_questions.md"))
            _verify_assumptions_registry(path=Path("docs/assumptions.md"))
            _verify_prompt_files(
                paths=[
                    Path("scripts/agent_prompt.txt"),
                    Path("scripts/question_prompt.txt"),
                    Path("scripts/worker_prompt.txt"),
                    Path("scripts/skeptic_prompt.txt"),
                    Path("scripts/supervisor_prompt.txt"),
                ],
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
        _verify_download_dir_hygiene(
            manifest_path=Path("resources/manifest.tsv"),
            downloads_dir=Path("resources/downloads"),
        )
        _verify_agent_brief(
            path=Path("docs/agent_brief.md"),
            max_lines=200,
            max_bytes=16_000,
            max_experiments=12,
        )
        _verify_agent_brief_structure(path=Path("docs/agent_brief.md"))
        _verify_open_questions_structure(path=Path("docs/open_questions.md"))
        _verify_assumptions_registry(path=Path("docs/assumptions.md"))
        _verify_prompt_files(
            paths=[
                Path("scripts/agent_prompt.txt"),
                Path("scripts/question_prompt.txt"),
                Path("scripts/worker_prompt.txt"),
                Path("scripts/skeptic_prompt.txt"),
                Path("scripts/supervisor_prompt.txt"),
            ],
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
