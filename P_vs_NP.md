# P vs NP - main notebook

**Status (2025):** The $\mathrm{P}$ vs $\mathrm{NP}$ problem remains open.
This notebook is a verifiable journal: statement, lemmas, barriers, and touchpoints for non-relativizing/non-natural ideas.

**Goal:** prove $\mathrm{P}\neq\mathrm{NP}$ or $\mathrm{P}=\mathrm{NP}$.
There is no proof yet; new ideas are recorded as lemmas with explicit dependencies
and counterexample checks.
## Navigation
- [0. Agreement on "formal verifiability"](docs/00_formal_verifiability.md)
- [1. Formal statement](docs/01_formal_statement.md)
- [2. Equivalent "certificate" formulation of NP](docs/02_np_certificates.md)
- [3. Basic inclusions](docs/03_basic_inclusions.md)
- [4. Reductions and NP-completeness](docs/04_reductions_np_complete.md)
- [5. SAT ≤p 3SAT](docs/05_sat_to_3sat.md)
- [6. 3SAT ≤p CLIQUE](docs/06_3sat_to_clique.md)
- [6.6. INDEPENDENT SET and VERTEX COVER](docs/06_6_is_vc.md)
- [7. Three barriers](docs/07_barriers.md)
- [8. Attack lines](docs/08_attack_lines.md)
- [Roadmap](docs/roadmap.md)
- [Agent brief (do not grow)](docs/agent_brief.md)
- [Open questions (queue)](docs/open_questions.md)
- [9. Circuit complexity](docs/09_circuit_complexity.md)
- [10. PARITY (depth 2)](docs/10_parity_depth2.md)
- [11. Switching lemma → PARITY ∉ AC⁰](docs/11_switching_lemma_ac0.md)
- [12. Time hierarchy](docs/12_time_hierarchy.md)
- [13. Savitch's theorem](docs/13_savitch.md)
- [14. Polynomial hierarchy](docs/14_ph.md)
- [15. Proof complexity: resolution and PHP](docs/15_proof_complexity.md)
- [16. IP = PSPACE and PCP](docs/16_ip_pcp.md)
- [17. Sources and reference links](docs/sources.md)
- [Formal layer (Lean 4)](formal/README.md)

## Verification
- Run checks (markdown + formalization): `scripts/verify_all.sh`
