# Assumption registry (External stubs)

This file tracks all `ASSUMPTION` stubs declared under `formal/External/`.
Final theorems must not depend on any of these.

## Summary

- Total stubs: 5

## Active stubs

| ID | Formal stub | Source | Notes |
| --- | --- | --- | --- |
| A-BGS | `formal/External/Barriers.lean` `bgs_relativization` | Baker–Gill–Solovay (1975) | Katz lecture p.1 (main result). |
| A-RR | `formal/External/Barriers.lean` `razborov_rudich_natural_proofs` | Razborov–Rudich (1997) | Thm. 4.1 p.3 (PRF assumption). |
| A-AW | `formal/External/Barriers.lean` `aaronson_wigderson_algebrization` | Aaronson–Wigderson (2008) | Thm. 5.3 p.23 (algebrizing oracles). |
| A-SAT3 | `formal/External/NPCompleteness.lean` `sat_to_3sat_correct` | Srba (2010) | Theorem “CNF-SAT ≤P 3SAT”, p.3/13. |
| A-3SATCLIQUE | `formal/External/NPCompleteness.lean` `three_sat_to_clique_correct` | Karp (1972) | p.9 “3SAT ≤P Clique”. |
