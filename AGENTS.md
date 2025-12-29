# AGENTS.md
# P vs NP - Verified‑First Research Notebook (Lean 4)

This file is the canonical protocol for agents working in this repo.
If it conflicts with any other document, follow **AGENTS.md**.

## 0) Non‑negotiables (read first)

**Truth lives in `formal/`.** Docs are navigation and rationale; they never “prove” anything.

**One run = exactly one artifact.** If you cannot finish one artifact, mark the item `BLOCKED` and stop.

**No `sorry` / `admit` / `axiom`** in:
- `formal/PvNP/Core/`
- `formal/WIP/Verified/`

**No folklore.** Any “known fact” must be backed by an **Exact citation**.

**Keep state bounded.** `docs/agent_brief.md` must not grow without bound.

---

## 1) Mission and “Solved” condition

### Mission
Build a strictly verified kernel that proves **either**:
- `P ≠ NP`, or
- `P = NP`

in the standard complexity model (deterministic vs nondeterministic polynomial time), with the final result reduced to Lean‑checked theorems.

### Solved criterion
Repository is “solved” only when:
1) `formal/PvNP/Main.lean` (or the repo’s designated entrypoint under `formal/PvNP/`) contains:
   - `theorem P_ne_NP : P ≠ NP` **or** `theorem P_eq_NP : P = NP`,
2) `RUN_MODE=core scripts/verify_all.sh` passes,
3) the theorem depends only on:
   - lemmas proved in this repo under `formal/PvNP/Core/`, and
   - Lean + mathlib standard libraries (no ad‑hoc axioms).

---

## 2) Vocabulary (must use consistently)

- **Item**: an entry in `docs/open_questions.md`.
- **StepID**: unique run identifier `Qxx.Sy.slug`.
- **NextStepID**: the next intended StepID for that item.
- **LeanTarget**: the Lean file the Proof artifact must touch.
- **Artifact**: the single deliverable of a run (Proof / Counterexample / Exact citation / Toy / Reduction / Barrier).
- **Oracle**: the verification gate (`scripts/verify_all.sh`, plus any toy scripts).
- **InfoGain**: `0/1/2` (0 = no new verified/citable info, 1 = local progress, 2 = reusable progress).

---

## 3) Repository contract (minimal)

- `P_vs_NP.md` — short index (status + links), ≤ 1–2 screens.
- `docs/`
  - `open_questions.md` — active queue. Each ACTIVE item MUST include: `Priority`, `LeanTarget`, `NextStepID`.
  - `agent_brief.md` — bounded working memory (“Do‑not‑repeat” + current bottleneck).
  - `roadmap.md` — chosen track(s) and dependency tree.
  - `sources.md` — the only sources we actually rely on.
  - `planned.tsv` — queued artifacts (Commit = `PENDING`).
  - `artifacts.tsv` — completed artifacts (Commit = git hash).
- `formal/`
  - `PvNP/Core/` — authoritative definitions/proofs (no `sorry`/`axiom`).
  - `WIP/Verified/` — WIP proofs (still no `sorry`/`axiom`).
  - `WIP/Scratch/` — scratchpad (placeholders allowed; NOT proof artifacts).
  - `Notes/` — long-form reasoning as doc-comments; not proofs.
- `scripts/verify_all.sh` — canonical CI gate.

---

## 4) Trust model

A change is “accepted” only if it is one of:
- **Lean‑checked proof** (compiled, no forbidden tokens in Core/Verified), or
- **compiler‑checkable refactor** (renames/reorders, definitional cleanup) that still passes the oracle.

Anything not in the formal layer is treated as **non-authoritative**.
External statements enter the repo only as **Exact citations** in `docs/sources.md`
(and optionally as notes in `formal/Notes/*.lean`).

---

## 5) Semantic gate (anti‑noise)

In `formal/PvNP/Core/` and `formal/WIP/Verified/`:

### Forbidden
- Placeholder declarations like:
  - `def X : Prop := True`
  - `theorem X : True := by ...`
  - “annotation lemmas” with no mathematical content  
  Put these in `formal/Notes/*.lean` or `docs/`.

### Required: “usefulness”
Every new lemma/definition MUST satisfy at least one:
- used by a later lemma in the same file or in an aggregator (e.g. `Work.lean`),
- discharges a named `LeanTarget` goal in `formal/WIP/Scratch/`,
- or is tagged `@[simp]`/`@[aesop]` **and** demonstrably shortens a proof.

### No enumeration instead of theory
If you are about to add **>5 near-identical blocks** (especially `by decide` on constants):
**STOP** and generalize (parameterized def/lemma).

### Diff budget
- Proof artifact changes should stay within ~200 lines.
- If more is needed, split into multiple runs (multiple StepIDs).

---

## 6) Role: WORKER (strict)

You are a WORKER. Each run delivers exactly one artifact and then stops.

### Mandatory outputs per run
- Update exactly one item in `docs/open_questions.md` (status + `NextStepID` + short note).
- Update `docs/agent_brief.md` (bounded; add to Do‑not‑repeat if needed).
- Append one row to `docs/artifacts.tsv` (Commit = git hash).
- Run the oracle and commit.

---

## 7) Run contract (MUST print first)

At the start of each run, print:

```

Run contract

* SelectedItem: <id/title>
* Priority: P0/P1
* Artifact: Proof | Counterexample | Exact citation | Toy | Reduction | Barrier
* StepID: Qxx.Sy.slug
* LeanTarget: <path or N/A>
* Oracle: RUN_MODE=<docs|wip|core> scripts/verify_all.sh
* FilesToTouch: <explicit list>
* StopCondition: <what counts as “done” for this run>

```

---

## 8) Workflow (1 run = 1 artifact)

### 0) Read state
- Read `docs/agent_brief.md` (Do‑not‑repeat).
- Read `docs/open_questions.md`.

### 1) Pick one item
- Prefer `ACTIVE P0` unless blocked/cooldown.
- Pick `P1` only if all P0 are `BLOCKED`/cooldown.

### 2) Pick one lens (do not repeat lens in consecutive runs)
See §10.

### 3) Retrieval before invention
Before attempting a Lean proof:
- `rg` over `formal/` and `resources/text_cache/`.
- Use `#find`, `simp?`, `aesop?` when available.

### 4) Kill-first check (required)
Try to falsify fast:
- counterexample,
- reduction to known barrier,
- small toy case.

### 5) Produce exactly one artifact
See §9.

### 6) Barrier check (mandatory when touching separation/lower bounds)
Fill template in §11 (briefly in `docs/open_questions.md` or in `formal/Notes/*.lean`).

### 7) Verify + commit
- Choose `RUN_MODE`:
  - `docs` if only docs changed
  - `wip` if touching `formal/WIP/*`
  - `core` if touching `formal/PvNP/Core/*`
- Run: `scripts/verify_all.sh`
- Commit message:
  - `<StepID>: <ArtifactType> - <one-line summary>`

### If stuck
If the artifact cannot be completed:
- mark the item `BLOCKED`,
- write **one-line blocker**,
- set a new `NextStepID`,
- stop (no extra edits).

---

## 9) Artifacts (exactly one)

### A) Proof
**Goal:** add real Lean code (def/theorem) in `LeanTarget`.

Requirements:
- touches `formal/PvNP/Core/*.lean` **or** `formal/WIP/Verified/*.lean` only,
- compiles (oracle passes),
- no forbidden tokens in Core/Verified,
- adds a short doc note (5–15 lines) in `docs/` with a link to the file.

### B) Counterexample
**Goal:** an explicit construction/oracle/counterexample that refutes a candidate claim.

Requirements:
- record the exact statement refuted and the minimal assumptions needed,
- if possible, include a Lean snippet or toy code that checks the counterexample.

### C) Exact citation
**Goal:** pin down a relied-on fact precisely.

Requirements:
- authors, year, title,
- theorem/lemma number **and** page (or arXiv version + statement label),
- add 2–6 lines: how it closes/corrects the chosen item.

### D) Toy computation
**Goal:** reproducible small experiment that tests a limited case.

Requirements:
- fixed seed and preserved inputs,
- script/check committed under `scripts/` or `resources/`,
- record result + interpretation in ≤10 lines.

### E) Reduction / Equivalence (Exact)
**Goal:** a formally written reduction/equivalence between statements.

Requirements:
- best: formalized as a Lean theorem,
- docs note: exactly 5–10 lines + dependencies.

### F) Barrier certificate
**Goal:** demonstrate that a proposed line of attack hits a named barrier under explicit conditions.

Requirements:
- includes at least one Exact citation,
- explicitly maps the barrier to the current StepID claim.

---

## 10) Lenses (choose exactly one per run)

1) Equivalence / translation (reformulate the target)
2) Compression / canonization (normal forms)
3) Invariant (monotone parameter, potential function)
4) Duality (NP vs coNP, search vs decision)
5) Trade-off (time/space, depth/size, randomness/advice)
6) Communication / rank (matrices, protocols, lower bounds)
7) Algebraization (arithmetization, ideals, IPS/PC framing)
8) Model stress test (oracles / relativization)

---

## 11) Barrier protocol (mandatory template)

When the step touches separation/lower bounds, include:

```

BarrierCheck

* Relativization:

  * Relativizes?: yes/no/unknown
  * If no: which exact substep breaks under oracle access?
  * If yes/unknown: name an oracle scenario to test (and known oracle counterexamples if any)
* NaturalProofs:

  * Applicable?: yes/no
  * Largeness: >= 2^{-poly(n)} ? (or “rare”)
  * Constructivity: decidable in poly(2^n) from truth-table?
  * Usefulness: separates the circuit class from random functions?
  * Exit point: where do we leave the natural-proofs framework (if we do)?
* Algebrization:

  * Applicable?: yes/no
  * Algebraizing?: yes/no/unknown
  * If no: what feature is not preserved by extension oracles?
  * If yes/unknown: reduce to a known algebrization barrier statement
* Citations: [BGS75, RR97, AW08, ...]

```

---

## 12) Strategy (anti-drift)

Project chooses:
- **1 main track** and
- **≤ 1 auxiliary track**.

Must be recorded in `docs/roadmap.md` and briefly in `docs/agent_brief.md`.

Rule: **≥ 80%** of runs must be in the main track.

---

## 13) Control tasks (pipeline sanity)

Before attempting “new separation progress”, verify the pipeline on 3 known facts:

1) Relativization barrier (BGS-style) as Barrier certificate + Exact citation.
2) Natural proofs barrier (RR-style) as Exact citation + short conclusion.
3) Algebrization barrier (AW-style) as Exact citation + toy example.

These must pass `scripts/verify_all.sh` and be linkable from `P_vs_NP.md`.

---

## 14) Source policy

- Any “known” claim → **Exact citation** or do not assert it.
- Prefer primary sources (papers/books) over blogs.
- Every used source must appear in `docs/sources.md`.
- If a PDF is used, record it in `resources/manifest.tsv` and store it under `resources/`.

---

## 15) Text / bloat policy

- `P_vs_NP.md` stays short (status + links only).
- In `docs/`, write only new content (no long essays).
- Long reasoning belongs in `formal/Notes/<Topic>.lean` doc-comments.
- Split files if > 4000 lines or > 300 KB.

---

## 16) Anti-loop & progress gate

Each run must end with:
- `StepID: ...`
- `InfoGain: 0/1/2`
- exactly one artifact.

Forbidden:
- repeating StepIDs in the Do‑not‑repeat list,
- cosmetic edits without an artifact,
- producing 2 artifacts in one run.

---

## 17) Canonical barrier references (copy into docs/sources.md)

- [BGS75] Theodore Baker, John Gill, Robert Solovay.
  “Relativizations of the P = ? NP Question.”
  *SIAM Journal on Computing* 4(4):431–442, 1975.
  DOI: https://doi.org/10.1137/0204037

- [RR97] Alexander A. Razborov, Steven Rudich.
  “Natural Proofs.”
  *Journal of Computer and System Sciences* 55(1):24–35, 1997.
  DOI: https://doi.org/10.1006/jcss.1997.1494

- [AW08] Scott Aaronson, Avi Wigderson.
  “Algebrization: A New Barrier in Complexity Theory.”
  *Proc. 40th ACM STOC*, 2008, pp. 731–740.
  DOI: https://doi.org/10.1145/1374376.1374481
  (Open PDF often available from authors’ pages.)