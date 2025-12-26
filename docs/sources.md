## 17. Источники и опорные ссылки

Пометка:
- `External-stub:` источник используется как временная аксиома в `formal/External/`.
Пока таких стабов нет; при добавлении — указывать точный номер теоремы/страницу.

**Постановка и базовые учебники**
- Clay Mathematics Institute (формулировка P vs NP): ../resources/downloads/clay_p_vs_np.pdf
- M. Sipser, *Introduction to the Theory of Computation*: ../resources/downloads/sipser_book.html. External-stub: `formal/External/NPCompleteness.lean` (sat_to_3sat_correct).
- O. Goldreich, *P, NP, and NP‑Completeness* (конспект): ../resources/downloads/goldreich_np.pdf
- S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (draft PDF): ../resources/downloads/arora_barak.pdf
- A. Rao (2022), *Lecture 5: Hierarchy Theorems (CSEP 531)* (PDF):
  ../resources/downloads/uw_hierarchy_2022_lecture5.pdf

**Обзоры (статус и контекст)**
- L. Fortnow (2021), *Fifty Years of P Versus NP and the Possibility of the Impossible* (PDF): ../resources/downloads/fortnow_pvnp50_2021.pdf
- S. Aaronson (2017), *P = NP* (ECCC TR17-004, PDF): ../resources/downloads/aaronson_pnp_2017.pdf
- L. Fortnow (2009), *The Status of the P versus NP Problem* (CACM, PDF): ../resources/downloads/fortnow_cacm_2009.pdf
- D. van Melkebeek (2007), *A Survey of Lower Bounds for Satisfiability and Related Problems* (PDF):
  ../resources/downloads/van_melkebeek_2007_survey.pdf

**NP‑полнота**
- S. Cook (1971), *The Complexity of Theorem‑Proving Procedures* (Cook–Levin): ../resources/downloads/cook_1971.pdf
- R. Karp (1972), *Reducibility Among Combinatorial Problems* (PDF): ../resources/downloads/karp_1972.pdf, p.9 “3SAT ≤P Clique”. External-stub: `formal/External/NPCompleteness.lean` (three_sat_to_clique_correct).
- J. Srba (2010), *CNF-SAT ≤p 3SAT; NP-Completeness of CLIQUE* (PDF): ../resources/downloads/srba_np_completeness_2010.pdf, Theorem “CNF-SAT ≤P 3SAT” p.3/13. External-stub: `formal/External/NPCompleteness.lean` (sat_to_3sat_correct).

**Барьеры**
- Baker–Gill–Solovay (1975), *Relativizations of the P = ? NP Question* (`../resources/downloads/jkatz_relativization_2005.pdf`, Katz lecture p.1, main result). External-stub: `formal/External/Barriers.lean` (bgs_relativization).
- S. Arora, R. Impagliazzo, U. Vazirani (1992), *Relativizing versus Nonrelativizing Techniques:
  The Role of Local Checkability* (PDF): ../resources/downloads/arora_impagliazzo_vazirani_1992.pdf
- J. Katz (2005), *Relativizing the P vs. NP Question* (lecture notes, PDF): ../resources/downloads/jkatz_relativization_2005.pdf
- R. de Haan (2021), *Lecture 5:
  Relativization and the Baker-Gill-Solovay Theorem* (PDF): ../resources/downloads/uva_relativization_lecture5_2021.pdf
- Razborov–Rudich (1997), *Natural Proofs* (PDF): ../resources/downloads/razborov_rudich_1997.pdf, Thm. 4.1 p.3. External-stub: `formal/External/Barriers.lean` (razborov_rudich_natural_proofs).
- Aaronson–Wigderson (2008), *Algebrization: A New Barrier in Complexity Theory* (PDF): ../resources/downloads/aaronson_wigderson_2008.pdf, Thm. 5.3 p.23. External-stub: `formal/External/Barriers.lean` (aaronson_wigderson_algebrization).
- L. Chen, Y. Hu, H. Ren (2025), *New Algebrization Barriers to Circuit Lower Bounds via Communication Complexity of Missing-String* (PDF):
  ../resources/downloads/chen_hu_ren_2025_algebrization_barriers.pdf
- A. Razborov (2023), *Propositional proof complexity* (ECM survey, PDF): ../resources/downloads/razborov_2023_proof_complexity_ecm.pdf

**Bounded arithmetic (для EF / proof complexity)**
- S. Buss (1995), *Bounded Arithmetic and Propositional Proofs, Part I:
  Bounded Arithmetic* (PDF): ../resources/downloads/buss_1995_bounded_arithmetic_notes.pdf
- A. Razborov, *Bounded Arithmetic and Lower Bounds in Boolean Complexity* (PDF): ../resources/downloads/razborov_bobo.pdf
- J. Krajíček (1995), *Bounded Arithmetic, Propositional Logic, and Complexity Theory* (PDF):
  ../resources/downloads/krajicek_1995_bounded_arithmetic_book.pdf
- S. Cook, P. Nguyen (2010), *Logical Foundations of Proof Complexity* (PDF): ../resources/downloads/cook_nguyen_2010_logical_foundations.pdf

**Proof complexity**
- T. Pitassi, I. Tzameret (2016), *Algebraic Proof Complexity:
  Progress, Frontiers and Challenges* (PDF): ../resources/downloads/pitassi_tzameret_2016_algebraic_proof_complexity.pdf
- A. Atserias, M. Mahajan, J. Nordström, A. Razborov (2024), *Proof Complexity and Beyond* (Oberwolfach report, PDF):
  ../resources/downloads/atserias_etal_2024_proof_complexity_beyond.pdf
- A. Razborov (2023), *Propositional proof complexity* (ECM survey, PDF): ../resources/downloads/razborov_2023_proof_complexity_ecm.pdf
- Cook–Reckhow (1979), *The Relative Efficiency of Propositional Proof Systems* (PDF): ../resources/downloads/cook_reckhow_1979.pdf
- P. Pudlák (1998), *The Lengths of Proofs* (PDF): ../resources/downloads/pudlak_1998_lengths_of_proofs.pdf
- A. Urquhart (1996), *The Complexity of Propositional Proofs* (PDF):
  ../resources/downloads/urquhart_1996_complexity_of_propositional_proofs.pdf
- A. Urquhart (1987), *Hard Examples for Resolution* (PDF): ../resources/downloads/urquhart_1987_hard_examples_resolution.pdf
- J. Håstad (2020), *On small-depth Frege proofs for Tseitin for grids* (PDF): ../resources/downloads/hastad_2020_small_depth_frege_tseitin_grids.pdf
- N. Galesi, D. Itsykson, A. Riazanov, A. Sofronova (2019), *Bounded-depth Frege complexity of Tseitin formulas for all graphs*
  (ECCC TR19-069, PDF): ../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf
- M. Alekhnovich, A. A. Razborov (2011), *Satisfiability, branch-width and Tseitin tautologies* (PDF):
  ../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf
- N. Galesi, N. Talebanfard, J. Torán (2018), *Cops-Robber games and the resolution of Tseitin formulas*
  (ECCC TR18-170, PDF): ../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf
- D. J. Harvey, D. R. Wood (2014), *The Treewidth of Line Graphs* (PDF):
  ../resources/downloads/harvey_wood_2014_treewidth_line_graphs.pdf
- T. Pitassi, B. Rossman, R. A. Servedio, L.-Y. Tan (2016), *Poly-logarithmic Frege depth lower bounds via an expander switching lemma* (PDF):
  ../resources/downloads/pitassi_rossman_servedio_tan_2016_expander_switching_lemma.pdf
- P. Beame, C. Beck, R. Impagliazzo (2016), *Time-Space Trade-offs in Resolution: Superpolynomial Lower Bounds for Superlinear Space* (PDF):
  ../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf
- S. Buss (2002), *Some Remarks on Lengths of Propositional Proofs* (PDF): ../resources/downloads/buss_2002_proplengths.pdf
- S. Buss (2011), *Towards NP–P via Proof Complexity and Search* (PDF): ../resources/downloads/buss_2011_np_p_proof_complexity.pdf
- S. Buss (1997), *Propositional Proof Complexity: An Introduction* (PDF): ../resources/downloads/buss_1997_proof_complexity_intro.pdf
- Haken (1985), *The Intractability of Resolution* (`../resources/downloads/tss_proof_complexity_notes.pdf`).
- S. Buss (1987), *Polynomial Size Proofs of the Propositional Pigeonhole Principle* (PDF): ../resources/downloads/buss_1987_php_frege.pdf
- P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi, P. Pudlák, A. Woods (1992),
  *Exponential Lower Bounds for the Pigeonhole Principle* (PDF):
  ../resources/downloads/beame_et_al_1992_php_bounded_depth_frege.pdf
- M. L. Bonet, S. Buss, T. Pitassi (2002), *Are there Hard Examples for Frege Systems?* (PDF):
  ../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf
- M. L. Bonet, S. Buss (2002), *Size-Depth Tradeoffs for Boolean Formulae* (PDF):
  ../resources/downloads/bonet_buss_2002_size_depth_tradeoffs_boolean_formulae.pdf
- S. Buss, P. Clote (2002), *Cutting planes, connectivity, and threshold logic* (PDF): ../resources/downloads/buss_cutting_planes_notes.pdf
- J. Pich, R. Santhanam (2023), *Towards P ≠ NP from Extended Frege lower bounds* (PDF):
  ../resources/downloads/pich_santhanam_2023_ef_lower_bounds.pdf
- R. de Wolf, *Pigeonhole and resolution (notes; Haken lower bound)* (PDF): ../resources/downloads/de_wolf_resolutionlowerbound.pdf
- Ben‑Sasson–Wigderson (2001), *Short Proofs are Narrow—Resolution Made Simple* (PDF): ../resources/downloads/ben_sasson_wigderson_2001.pdf
- A. A. Tabatabai (2025), *Proof Complexity and Feasible Interpolation* (PDF): ../resources/downloads/tabatabai_2025_feasible_interpolation.pdf
- D. Itsykson, V. Oparin (2013), *Graph expansion, Tseitin formulas and resolution proofs for CSP* (PDF):
  ../resources/downloads/itsykson_oparin_2013_tseitin.pdf
- M. Lauria (2015), *Lecture 2: Resolution Lower Bounds via the Pigeonhole Principle* (PDF): ../resources/downloads/lauria_lecture2_2015.pdf
- University of Toronto (TSS, 2021), *Introduction to Proof Complexity* (notes, PDF): ../resources/downloads/tss_proof_complexity_notes.pdf

**Неравномерность (P/poly)**
- Karp–Lipton (1980), *Some connections between nonuniform and uniform complexity classes*
  (`../resources/downloads/trevisan_lecture05_2008.pdf`).
- L. Trevisan (2008), *Lecture 5: The Karp-Lipton-Sipser Theorem* (notes, PDF): ../resources/downloads/trevisan_lecture05_2008.pdf

**Схемные нижние оценки и техника**
- Furst–Saxe–Sipser (1984), *Parity, circuits, and the polynomial-time hierarchy* (PDF): ../resources/downloads/fss_1984.pdf
- J. Håstad (1986), *Almost Optimal Lower Bounds for Small Depth Circuits* (PDF): ../resources/downloads/hastad_1986.pdf
- R. Smolensky (1987), *Algebraic methods in the theory of lower bounds for Boolean circuit complexity* (PDF):
  ../resources/downloads/smolensky_1987.pdf
- A. Razborov (1985), *Lower bounds for the monotone complexity of some Boolean functions* (PDF):
  ../resources/downloads/razborov_1985_monotone.pdf
- S. Grewal, V. M. Kumar (2024), *Improved Circuit Lower Bounds and Quantum-Classical Separations* (PDF):
  ../resources/downloads/grewal_kumar_2024_gc0.pdf
- R. O’Donnell (курс/лекции; switching lemma и AC⁰‑нижние оценки): ../resources/downloads/odonnell_course.html
- R. O’Donnell (2009), *Lecture 14: The Switching Lemma* (PDF): ../resources/downloads/odonnell_lecture14.pdf

**Алгебраические подходы (GCT)**
- M. Bläser, C. Ikenmeyer (2025), *Introduction to Geometric Complexity Theory* (PDF):
  ../resources/downloads/blaser_ikenmeyer_2025_gct_intro.pdf
- R. Saptharishi (2016), *A survey of lower bounds in arithmetic circuit complexity* (PDF):
  ../resources/downloads/saptharishi_2016_arithmetic_circuit_survey.pdf

**PCP**
- S. Arora, S. Safra (1998), *Probabilistic Checking of Proofs:
  A New Characterization of NP* (PDF): ../resources/downloads/arora_safra_1998_pcp.pdf
- S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy (1998), *Proof Verification and the Hardness of Approximation Problems* (PDF):
  ../resources/downloads/almss_1998_pcp.pdf
- I. Dinur (2007), *The PCP Theorem by Gap Amplification* (PDF): ../resources/downloads/dinur_2007_pcp.pdf



**Интерактивные доказательства и дерэндомизация**
- A. Shamir (1992), *IP = PSPACE* (PDF): ../resources/downloads/shamir_1992.pdf
- N. Nisan, A. Wigderson (1994), *Hardness vs. Randomness* (PDF): ../resources/downloads/nisan_wigderson_1994.pdf


**Примечание.** Термин $\mathrm{Time}[n^k]/u(n)$ фиксирован в разделе 9;
схема $w_{n,k,u}(f)$ — в разделе 15.7.
(Локальный манифест ссылок/скачивалка: `../resources/manifest.tsv`, `../resources/download_resources.py`; скачанные PDF: `../resources/downloads/`.)
