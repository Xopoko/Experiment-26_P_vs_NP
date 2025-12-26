# Assumption registry (External stubs)

This file tracks all `ASSUMPTION` stubs declared under `formal/External/`.
Final theorems must not depend on any of these.

## Summary

- Total stubs: 5

## Active stubs

| ID | Formal stub | Source | Notes |
| --- | --- | --- | --- |
| A-BGS | `formal/External/Barriers.lean` `bgs_relativization` | Baker–Gill–Solovay (1975) | Relativization barrier. |
| A-RR | `formal/External/Barriers.lean` `razborov_rudich_natural_proofs` | Razborov–Rudich (1997) | Natural proofs barrier (PRF assumption). |
| A-AW | `formal/External/Barriers.lean` `aaronson_wigderson_algebrization` | Aaronson–Wigderson (2008) | Algebrization barrier. |
| A-SAT3 | `formal/External/NPCompleteness.lean` `sat_to_3sat_correct` | Sipser (NP-completeness); Srba (2010) | SAT ↔ 3SAT equisatisfiability. |
| A-3SATCLIQUE | `formal/External/NPCompleteness.lean` `three_sat_to_clique_correct` | Karp (1972) | 3SAT ↔ CLIQUE correctness. |
