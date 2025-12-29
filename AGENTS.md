# AGENTS.md

# P vs NP - Verified-First Research Notebook

## Mission

The goal of the project is to prove or refute the hypothesis **P != NP** in the standard computing model
(polynomial time on a deterministic Turing machine vs nondeterministic),
with the result reduced to a **strictly verified kernel**.

**Solved criterion:**

- There is a main formal file in the repository (see `formal/`) with a theorem of the form:
  - `theorem P_ne_NP : P ≠ NP` (or `P_eq_NP : P = NP`),
  - which **compiles** in the proof assistant (Lean/Coq/Isabelle - choose one),
  - and depends only on lemmas that:
    1) formally proved in the same tree, or
    2) imported from the official standard library (mathlib/Coq stdlib/...).

Markdown text (`docs/`) is **readable navigation and explanation**, but **the truth is in `formal/`**.
Doc-comments in `formal/Notes/*.lean` are notes, not formal proofs.

---

## Repository: minimal structure

- `P_vs_NP.md` -- short status and links (no more than 1-2 screens).
- `docs/`
  - `roadmap.md` -- selected tracks and "dependency tree".
  - `open_questions.md` -- active backlog of micro-issues (with NextStepID).
  - `agent_brief.md` -- project RAM (with Do-not-repeat).
  - `planned.tsv` -- planned artifact queue (Commit = PENDING).
  - `artifacts.tsv` -- completed artifact log (Commit = git hash).
  - `sources.md` -- exactly the sources we actually rely on.
- `formal/`
- `PvNP/Core/` -- definitions and proofs.
  - `Notes/` -- long research notes in Lean (doc-comments, Lean-first).
- `scripts/`
  - `verify_notebook.py` -- checks markdown structure (if present).
  - `verify_all.sh` -- general CI gate: markdown + formalization.
- `agent/logs/` -- run logs (optional).

---

## Trust model

Any artifact of type `Proof` is considered "accepted" only if:

- there is a Lean proof (formally compiled), or
- it is a trivial step that can be checked by the compiler (like a definition refactor).

External statements are captured **only** as exact references in `docs/sources.md`
and/or as notes in `formal/Notes/*.lean` (without adding axioms).

---

## Role: WORKER

In each run you are a WORKER.
You take **exactly 1 research step** and deliver a verifiable artifact
(see "Artifacts").

Required actions:

- update one item `docs/open_questions.md` (status + NextStepID),
- update `docs/agent_brief.md` (short, without growth),
- drive away `scripts/verify_all.sh`,
- make 1 commit with a meaningful message.

Note: active questions in `docs/open_questions.md` must have `LeanTarget:`
to link Proof steps to a specific Lean file.

---

## Research mode: 1 run = 1 artifact

### WORKER steps (strict protocol)

0) Read `docs/agent_brief.md` and check Do-not-repeat.
1) Select 1 active item from `docs/open_questions.md`.
   - If any ACTIVE P0 is not in cooldown, pick it.
   - Pick P1 only if all P0 are BLOCKED/cooldown.
2) Pick **one** lens (see below) - don't repeat a lens 2 runs in a row.
3) Formulate a **formal statement** (definitions + quantifiers).
   - Before a Lean proof attempt, run retrieval: `rg` in `formal/` and `resources/text_cache/`.
   - If Lean tools are available, try `#find` / `simp?` / `aesop?` to locate lemmas.
4) Do a toy test/limited case and try to **kill** the idea first:
   - counterexample,
   - reduction to the known,
   - emphasis on the barrier.
5) If you survived: bring it to one artifact (below).
6) Mandatory barrier protocol: relativization / natural proofs / algebrization (not in words, but according to a template).
7) Update `open_questions.md` And `agent_brief.md`.
8) `scripts/verify_all.sh` -> commit.

Note: if you cannot add Lean code, choose an artifact **not Proof**.

---

## Artifacts (exactly one per launch)

Choose one type and produce it completely.

Artifact logs:
- `docs/artifacts.tsv` records completed artifacts only (Commit = git hash).
- `docs/planned.tsv` records queued/planned items only (Commit = PENDING).

### 1) Proof

- Must contain **real Lean code** (not just the text in doc-comments).
- Add or change `def`/`theorem` V `formal/PvNP/Core/*.lean` (or another kernel `formal/`).
- The file is compiled, `scripts/verify_all.sh` passes.
- IN `docs/` add a short "human" comment of 5-15 lines and a link to the file.

### 2) Counterexample

- Explicit counterexample/oracle/construction.
- If possible, formalize it as a small lemmatic fact or at least a toy code.
- IN `docs/` record: what exactly is refuted, what conditions are needed.

### 3) Exact citation

- Don't rewrite "folklore".
- Give the exact source: authors, year, title, **theorem/lemma number/page**.
- IN `docs/` add 2-6 lines: how this closes/corrects the open_questions item.

### 4) Toy computation

- Small experiment/brute force/script that tests a limited case.
- The result must be reproducible (fixed seed, inputs preserved).

### 5) Reduction/Equivalence (Exact)

- Formally written reduction/equivalence between statements.
- Ideal: formalized as a theorem.
- IN `docs/` -- exactly 5-10 lines of meaning + dependencies.

### 6) Barrier certificate

- A short document that the chosen line inevitably runs into a barrier under these conditions.
- Required: exact source (Exact citation) and explicit link to your step.

---

## Lenses (choose one)

1) Equivalence (translation to another object/formulation)
2) Compression/canonization (effective normalization)
3) Invariant (monotonic parameter)
4) Duality (NP vs coNP, search vs decision)
5) Trade-off (time-space, depth-size, randomness-advice)
6) Communication/rank (matrices, protocols, lower bounds)
7) Algebraization (IPS/PC, arithmetization, ideals)
8) Model stress test (oracles/relativization)

---

## Barrier protocol (mandatory, according to template)

At the end of each step (in the step note in `formal/Notes/*.lean` or briefly in `docs/open_questions.md`) fill in:

When the step touches separation/lower bounds, include canonical barrier citations
(Baker-Gill-Solovay 1975, Razborov-Rudich 1997, Aaronson-Wigderson 2008) and ensure
they are listed in `docs/sources.md`.

### A) Relativization check

- `Relativizes?` yes/no/not sure.
- If "no": indicate the **specific step** that breaks when adding an oracle (what exactly uses "non-relativizing" information).
- If "yes/not sure": try to formulate an oracle option and check if
  whether a well-known counterexample oracle appears.

### B) Natural proofs check

If the step concerns **schematic lower bounds via a property of functions**, evaluate:

- `Largeness`: property has density >= 2^{-poly(n)}? (or "rare"?)
- `Constructivity`: recognized as poly(2^n) by truth table?
- `Usefulness`: Does the circuit class C separate from the random function?
  And indicate: **where exactly you leave** the framework of natural proofs (if you do).

### C) Algebrization check

If arithmetization/polynomial extensions are used:

- Indicate whether the method is "algebraizing".
- If not: explain specifically what is not saved with "extension oracle".
- If yes/not sure: try to reduce it to a known barrier.

---

## Strategy (required: choose a track and stick to it)

The project selects **1 main track** and a maximum of **1 auxiliary**.
This is recorded in `docs/roadmap.md` and briefly in `docs/agent_brief.md`.

Recommended tracks (example):

- Track A: Circuit lower bounds (NP  P/poly) + bypass natural proofs
- Track B: Proof complexity / IPS / lower bounds -> transfer to diagrams
- Track C: Algorithmic approach "derive unexpectedly fast algorithms from P=NP"
- Track D: Algebraic Complexity / GCT (if competent)

**Rule:** 80% of the steps must be in the main track. Otherwise, there is drift and no progress.

---

## Control tasks (to make sure the pipeline is running)

Before a "real breakthrough", it is necessary to run on 3 known facts:

1) Relativization: issue it as Barrier certificate + Exact citation.
2) Natural proofs: format definitions + barrier as Exact citation and short conclusion.
3) Algebrization: format it as Exact citation + toy example "why arithmetization doesn't save."

These 3 must be verified by the pipeline (verify_all + clear links).

---

## Source policy and search

- Any "known" -> either `Exact citation`, or don't write.
- Links should be primary sources (article/book), not blogs, if possible.
- Each source actually used is recorded in `docs/sources.md`
  and (if any) is placed in `resources/` with manifest.

---

## Text policy (to prevent the repository from becoming bloated)

- `P_vs_NP.md` - very short, only status and links to key files.
- IN `docs/` We write only new mathematical content.
- Long discussions - in `formal/Notes/<Topic>.lean` (doc-comments).
- If the file is > 4000 lines or > 300KB, we split it into topics.

---

## Anti-loop & progress gate

Each run ends:

- `StepID: Qxx.Sy.slug` (unique)
- `InfoGain: 0/1/2`
- and exactly one artifact.

Forbidden:

- repeat StepID from `Do-not-repeat` V `docs/agent_brief.md`,
- make "cosmetic" edits without an artifact,
- make 2 artifacts per run.

If it doesn't work:

- mark the item as `BLOCKED`,
- write 1 line "blocker",
- assign a new NextStepID,
- stop.

---

## Git and CI

Before commit:

- `scripts/verify_all.sh`

Commit message:

- `<StepID>: <artifact type> - <one-line summary>`

---
