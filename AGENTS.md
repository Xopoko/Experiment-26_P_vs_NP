# AGENTS.md
# P vs NP — Verified‑First Research Notebook (Lean 4)

This file is the canonical agent protocol for this repo.
If it conflicts with any other doc, follow **AGENTS.md**.

## 0) Hard rules (non‑negotiables)

- **Truth lives in `formal/`.** Docs are navigation; they do not prove anything.
- **One run = exactly one artifact.** If you cannot finish one artifact: mark the item `BLOCKED`, write 1‑line blocker, set `NextStepID`, stop.
- **No `sorry` / `admit` / `axiom`** in:
  - `formal/PvNP/Core/`
  - `formal/WIP/Verified/`
- **No folklore.** Any “known fact” must be backed by an **Exact citation**.
- **No bloat.** Keep `docs/agent_brief.md` bounded; long reasoning goes to `formal/Notes/*.lean` (doc-comments).

---

## 1) Mission and “Solved” criterion

### Mission
Prove or refute **P ≠ NP** in the standard model (deterministic vs nondeterministic polynomial time),
reducing the result to a **Lean-verified kernel**.

### Solved criterion
Repo is “solved” only when:
1) `formal/PvNP/Main.lean` (or the designated entrypoint under `formal/PvNP/`) contains:
   - `theorem P_ne_NP : P ≠ NP` **or** `theorem P_eq_NP : P = NP`,
2) `RUN_MODE=core scripts/verify_all.sh` passes,
3) the theorem depends only on:
   - lemmas proved in this repo under `formal/PvNP/Core/`, and
   - Lean + mathlib standard libraries (no ad‑hoc axioms).

---

## 2) Repository contract (minimal)

- `P_vs_NP.md` — short index (status + links), ≤ 1–2 screens.
- `docs/`
  - `open_questions.md` — active queue; each ACTIVE item MUST include: `Priority`, `LeanTarget`, `NextStepID`.
  - `agent_brief.md` — bounded working memory, includes “Do‑not‑repeat”.
  - `roadmap.md` — track(s) + dependency tree.
  - `sources.md` — the only sources we actually rely on.
  - `planned.tsv` — planned artifacts (Commit = `PENDING`).
  - `artifacts.tsv` — completed artifacts (Commit = git hash).
- `formal/`
  - `PvNP/Core/` — authoritative definitions/proofs (no `sorry`/`axiom`).
  - `WIP/Verified/` — WIP proofs (still no `sorry`/`axiom`).
  - `WIP/Scratch/` — scratchpad (placeholders allowed; NOT proof artifacts).
  - `Notes/` — long notes as Lean doc-comments; not proofs.
- `scripts/verify_all.sh` — canonical oracle gate (docs + formal).

---

## 3) Trust model

Accepted artifacts are:
- **Lean‑checked proofs** (compiled; no forbidden tokens in Core/Verified), or
- **compiler-checkable refactors** (renames/reorders/cleanup) that still pass the oracle.

Anything outside `formal/` is **non-authoritative** and must be treated as notes unless it is an Exact citation.

---

## 4) Semantic gate (anti‑noise)

In `formal/PvNP/Core/` and `formal/WIP/Verified/`:

### Forbidden
- Placeholder declarations like:
  - `def X : Prop := True`
  - `theorem X : True := by ...`
  - any “annotation lemma” with no mathematical content  
  Put these into `formal/Notes/*.lean` or `docs/`.

### Required: usefulness
Every new lemma/definition MUST satisfy at least one:
- used by a later lemma in the same file or in an aggregator (e.g. `Work.lean`),
- discharges an explicit `LeanTarget` goal in `formal/WIP/Scratch/`,
- or is tagged `@[simp]`/`@[aesop]` **and** demonstrably shortens a proof.

### No enumeration instead of theory
If you are about to add **>5 near-identical def/theorem blocks** (especially `by decide` on constants):
**STOP** and generalize (parameterized def/lemma).

### Diff budget
- Proof artifacts: target ≤ ~200 lines changed.
- If more is needed: split into multiple runs (multiple StepIDs).

---

## 5) Role: WORKER (strict)

Each run: pick exactly one open item and deliver exactly one artifact.

### Mandatory outputs per run
- Update exactly one item in `docs/open_questions.md` (status + `NextStepID` + short note).
- Update `docs/agent_brief.md` (bounded; update Do‑not‑repeat when needed).
- Append exactly one row to `docs/artifacts.tsv` (Commit = git hash).
- Run oracle + make exactly one git commit.

---

## 6) Run contract (print first)

At the start of each run, print:

```text
Run contract
- SelectedItem: <id/title>
- Priority: P0/P1
- Artifact: Proof | Counterexample | Exact citation | Toy | Reduction | Barrier
- StepID: Qxx.Sy.slug
- LeanTarget: <path or N/A>
- Oracle: RUN_MODE=<docs|wip|core> scripts/verify_all.sh
- FilesToTouch: <explicit list>
- StopCondition: <what counts as “done” for this run>
```

---

## 7) Workflow (1 run = 1 artifact)

0. Read `docs/agent_brief.md` (Do‑not‑repeat) and `docs/open_questions.md`.
1. Pick one ACTIVE item:

   * prefer `ACTIVE P0` unless blocked/cooldown,
   * pick `P1` only if all P0 are blocked/cooldown.
2. Pick exactly one lens (do not repeat lens in consecutive runs).
3. Retrieval before invention:

   * `rg` over `formal/` and `resources/text_cache/`,
   * use `#find`, `simp?`, `aesop?` if available.
4. Kill-first check (required): try to falsify quickly (counterexample / toy case / barrier hit).
5. Produce exactly one artifact (see §8).
6. Barrier check (mandatory when touching separation/lower bounds): fill template §10.
7. Choose `RUN_MODE` for verification:

   * `RUN_MODE=docs` if only docs/notes changed,
   * `RUN_MODE=wip` if touching `formal/WIP/*`,
   * `RUN_MODE=core` if touching `formal/PvNP/Core/*`.
     Run `scripts/verify_all.sh`.
8. Commit with message:

   * `<StepID>: <ArtifactType> - <one-line summary>`

### If stuck

If the artifact cannot be completed:

* mark item `BLOCKED`,
* write 1‑line blocker,
* set a new `NextStepID`,
* stop (no extra edits).

---

## 8) Artifacts (exactly one)

### A) Proof

Goal: add real Lean code (def/theorem) in the item’s `LeanTarget`.

Requirements:

* modify only `formal/PvNP/Core/*.lean` or `formal/WIP/Verified/*.lean`,
* oracle passes,
* no forbidden tokens in Core/Verified,
* add a short doc note (5–15 lines) in `docs/` with a link to the Lean file.

### B) Counterexample

Goal: explicit construction/oracle/counterexample that refutes a candidate claim.

Requirements:

* record the exact statement refuted + minimal assumptions,
* include a Lean snippet or toy code if feasible.

### C) Exact citation

Goal: precisely pin down a relied-on fact.

Requirements:

* authors, year, title,
* theorem/lemma number and page (or arXiv version + statement label),
* add 2–6 lines: how it closes/corrects the chosen open item.

### D) Toy computation

Goal: reproducible small experiment testing a limited case.

Requirements:

* fixed seed + preserved inputs,
* script committed under `scripts/` or `resources/`,
* record result + interpretation in ≤10 lines.

### E) Reduction / Equivalence (Exact)

Goal: formally written reduction/equivalence between statements.

Requirements:

* best: a Lean theorem,
* docs note: exactly 5–10 lines + dependencies.

### F) Barrier certificate

Goal: show the chosen approach inevitably runs into a barrier under explicit conditions.

Requirements:

* includes at least one Exact citation,
* explicitly maps the barrier to the StepID’s claim.

---

## 9) Lenses (choose exactly one per run)

### Core lenses (default; use most of the time)

1. Equivalence / translation (reformulate the target)
2. Compression / canonization (normal forms)
3. Invariant (monotone parameter / potential function)
4. Duality (NP vs coNP, search vs decision)
5. Trade-off (time/space, depth/size, randomness/advice)
6. Communication / rank (matrices, protocols, lower bounds)
7. Algebraization (arithmetization, ideals, IPS/PC framing)
8. Model stress test (oracles / relativization)

### Aux lenses (allowed, but limited to avoid drift)

Rule: **Aux lenses must be ≤ 30% of runs** overall.
Do not use the same aux lens in consecutive runs.

9. Library mining (lemma extraction)
   - goal: extract “bottleneck” lemmas/defs that unblock multiple proofs
   - typical artifact: Proof / Reduction

10. Automation / tactic engineering
   - goal: stabilize and shorten proofs (`simp` sets, `aesop` rules, helper lemmas)
   - typical artifact: Proof (with measurable simplification)

11. Specification / definitions audit
   - goal: strengthen types/definitions (remove “discipline-only” invariants; prefer `Fin n → _` / `Vector _ n`)
   - typical artifact: Proof (refactor) / Reduction (equivalence old↔new)

12. Counterexample / adversarial testing
   - goal: actively search minimal counterexamples to candidate statements
   - typical artifact: Counterexample / Toy computation

13. Parameter sweep / empirical map
   - goal: map where a claim holds/fails in bounded regimes (small n, restricted models)
   - typical artifact: Toy computation (+ short interpretation)

14. Complexity bookkeeping / asymptotics hygiene
   - goal: disambiguate growth (bases of log/exp, domains, hidden parameters); extract reusable growth lemmas
   - typical artifact: Proof / Exact citation

15. Meta-reduction planning (dependency graph / bottleneck analysis)
   - goal: build a small dependency graph and pick the highest-leverage next lemma/definition
   - typical artifact: Reduction/Equivalence (Exact) or docs note that updates NextStepID(s)

16. Barrier-driven design
   - goal: design steps with an explicit intended “exit point” from barriers (or a certified barrier hit)
   - typical artifact: Barrier certificate (often paired with Proof/Toy in a later run)

---

## 10) Barrier protocol (mandatory template)

When the step touches separation/lower bounds, include:

```text
BarrierCheck
- Relativization:
  - Relativizes?: yes/no/unknown
  - If no: which exact substep breaks under oracle access?
  - If yes/unknown: name an oracle scenario to test (and known oracle counterexamples if any)
- NaturalProofs:
  - Applicable?: yes/no
  - Largeness: >= 2^{-poly(n)} ? (or “rare”)
  - Constructivity: decidable in poly(2^n) from truth-table?
  - Usefulness: separates the circuit class from random functions?
  - Exit point: where do we leave the framework (if we do)?
- Algebrization:
  - Applicable?: yes/no
  - Algebraizing?: yes/no/unknown
  - If no: what feature is not preserved by extension oracles?
  - If yes/unknown: reduce to a known algebrization barrier statement
- Citations: [BGS75, RR97, AW08, ...]
```

---

## 11) Strategy (anti‑drift)

Project chooses:

* 1 main track, and
* ≤ 1 auxiliary track.

Must be recorded in `docs/roadmap.md` and briefly in `docs/agent_brief.md`.

Rule: **≥ 80%** of runs must be in the main track.

---

## 12) Control tasks (pipeline sanity)

Before “new separation progress”, verify the pipeline on 3 known facts:

1. Relativization barrier as Barrier certificate + Exact citation.
2. Natural proofs barrier as Exact citation + short conclusion.
3. Algebrization barrier as Exact citation + toy example.

All must pass `scripts/verify_all.sh` and be linkable from `P_vs_NP.md`.

---

## 13) Asymptotics hygiene (when used)

If writing asymptotic claims:

* always disambiguate `exp`: `e^x` vs `2^x`;
* remember `exp((log n)^k)` for `k>1` is superpolynomial (clarify base);
* if you rely on a standard theorem: it must be an Exact citation.

---

## 14) Source policy

* Any “known” claim → Exact citation or do not assert it.
* Prefer primary sources (papers/books) over blogs.
* Every used source must appear in `docs/sources.md`.

---

## 15) Anti‑loop & progress gate

Each run must end with:

* `StepID: ...`
* `InfoGain: 0/1/2`
* exactly one artifact.

Forbidden:

* repeating StepIDs in Do‑not‑repeat,
* cosmetic edits without an artifact,
* producing 2 artifacts in one run.

---

## 16) Canonical barrier references (add to docs/sources.md)

* [BGS75] Baker, Gill, Solovay. “Relativizations of the P = ? NP Question.” SIAM J. Comput., 1975. doi:10.1137/0204037
* [RR97] Razborov, Rudich. “Natural Proofs.” JCSS, 1997. doi:10.1006/jcss.1997.1494
* [AW08] Aaronson, Wigderson. “Algebrization: A New Barrier in Complexity Theory.” STOC 2008. doi:10.1145/1374376.1374481
