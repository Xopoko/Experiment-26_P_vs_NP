# Open questions (work queue)

Rule: **each agent run selects exactly 1 item below** and makes measurable progress:
`Proof` / `Counterexample` / `Exact citation` / `Toy` / `Reduction` / `Barrier` + barrier check.
Then it updates the item.
Each active item contains `Success`, `PublicSurface`, `LeanTarget`, `Attempts`,
`LastOutcome`, `BlockerType`, `TimeBudget`, `Deps`, `DefinitionOfDone`, and oracle fields
(`Oracle`, `OraclePass`, `StopRule`) unless it is an `Exact citation`.
If `BarrierCheckRequired: yes`, then the block `BarrierCheck` required.

## Active

- [ ] **Q39 (Tseitin(Grid): depth gap for polynomial size in bounded-depth Frege):**

  - `Priority:` P1
  - `Status:` BLOCKED
  - `LastStepID:` Q39.S154-oracle-xor-nonrelativizing-exit
  - `NextStepID:` Q39.S155-contiguous-alt-shift-classification
  - `LeanTarget:` formal/WIP/Verified/Q39.lean
  - `BarrierCheckRequired:` yes
  - `Lens:` Model stress test (oracle).
  - `Artifact:` Barrier.
  - `Oracle:` `python3 scripts/toy_q39_rank2.py --alt 118`
  - `OraclePass:` exit 0 and report `rank=2` (nonzero distinct vectors).
  - `StopRule:` reached >5 consecutive contiguous alt-shifts with rank=2 (now alt54..alt117);
    stop extending and switch to classification or a barrier certificate; if rank!=2, record the failure and stop.
  - `Attempts:` 10
  - `LastOutcome:` BLOCKED
  - `BlockerType:` BARRIER_RELATIVIZATION
  - `TimeBudget:` 2h
  - `Deps:` `formal/WIP/Verified/Q39.lean`, `scripts/toy_q39_rank2.py`
  - `DefinitionOfDone:` classify the contiguous alt-shift regime or find a non-relativizing escape; document whichever path is taken (see `Q39.S155-contiguous-alt-shift-classification`).
  - `Update:` Barrier certificate recorded in `docs/q39_s154.md`.
  - `PublicSurface:` `scripts/toy_q39_rank2.py`, `formal/WIP/Verified/Q39.lean`
    (contiguous alt-shift vectors up to alt117).
  - `BarrierCheck:`
    - `A) Relativization check:` Relativizes? yes (rank-only reasoning is oracle-agnostic). See `docs/q39_s154.md` for the oracle-XOR test and the BGS75 separation.
    - `B) Natural proofs check:` Applicable? yes (if the rank witness upgrades to a large constructive property). Largeness/constructivity unknown. Exit point: use a non-natural or non-constructive witness. [RR97]
    - `C) Algebrization check:` Applicable? unknown. If yes/unknown: reduce to an AW08-style algebrizing oracle.
  - `Success:` either an explicit upper at depth $O(\log N/\log\log N)$, or a barrier/counterexample for the "XOR step" in bounded-depth Frege (see `docs/q39_s154.md`).
    Context: node - syntactically simulate Gaussian elimination step; fixed partitions break, even-batching does not help.
    Note: the orientation invariance of the frontier is fixed in `formal/WIP/Verified/Q39.lean`.
    Details: `formal/Notes/TseitinQ39.lean` (Section 16.153-Section 16.177) and summary in `formal/Notes/TseitinLocalEF.lean` §16.187.
- [ ] **Q43 (flat local-EF(s): are there "small" evaluations for poly-size proofs?):**

  - `Priority:` P0
  - `Status:` BLOCKED
  - `LastStepID:` Q43.S366-escape-natural-proof
  - `NextStepID:` Q43.S366-escape-natural-proof
  - `LeanTarget:` formal/WIP/Verified/Q43.lean
  - `Oracle:` `python3 scripts/toy_q43_gap_sqrt2.py`
  - `OraclePass:` exit 0 with all k-lines ending `-> ok` (failures: 0; k=12..104).
  - `StopRule:` if uniform `k ≥ 12` is insufficient to recover the global gap-min bridge, record the dependency and stop.
  - `Attempts:` 23
  - `LastOutcome:` BLOCKED
  - `BlockerType:` BARRIER_ENTROPY
  - `TimeBudget:` 2h
  - `Deps:` `formal/WIP/Verified/Q43.lean`, `scripts/toy_q43_gap_sqrt2.py`
  - `DefinitionOfDone:` wait for the entropy-stopper score to drop or introduce a substantively different artifact before reattempting the non-natural support predicate (Q43.S366).
  - `GeneralizationTarget:` define `n_k := floor(sqrt(2^(2k+1)-1))`, show the log2 jump at `n_k^2`,
    then derive a general gap-drop lemma from the jump.
  - `BarrierCheckRequired:` no
  - `PublicSurface:` `formal/WIP/Verified/Q43.lean`
    (Q43_nk, Q43_log2_jump_nk, Q43_grid_ratio_drop_nk_of_ge, Q43_grid_ratio_drop_nk,
    Q43_gap_n_succ_eq, Q43_gap_min_ratio_drop_global,
    Q43_log2_poly_bound, Q43_tParam_le_log2_poly_bound, Q43_tParam_lineMax_le_log2_poly_bound,
    Q43_tParam_le_polylog_of_quasipoly, Q43_tParam_lineMax_le_polylog_of_quasipoly,
    Q43_tParam_lineMax_le_polylog_of_quasipoly_grid,
    Q43_quasipoly_grid_eval_bounds, Q43_tParam_lineMax_le_polylog_of_quasipoly_grid_twice,
    Q43_thm41_log2_threshold_c1_grid_param_of_scaled,
    Q43_thm41_log2_threshold_c1_grid_param_of_quasipoly,
    Q43_thm41_log2_threshold_c1_grid_param_of_log2,
    Q43_thm41_regime_d_ok_param_of_log2,
    Q43_thm41_c1_le_grid_of_scaled,
    Q43_thm41_regime_d_ok_param_of_scaled,
    Q43_thm41_regime_d_ok_param_of_gap_right_n0,
    Q43_quasipoly_regime_d_ok_param_lineMax_of_gap_right,
    Q43_quasipoly_regime_d_ok_param_lineMax,
    Q43_quasipoly_regime_d_ok_param_tParam,
    Q43_flat_eval_statement,
    Q43_flat_eval_statement_of_quasipoly,
    Q43_flat_eval_statement_of_quasipoly_gap_right,
    Q43_flat_eval_statement_of_quasipoly_gap_band_k,
    Q43_flat_eval_statement_of_quasipoly_gap_band_log2,
    Q43_hrThreshold_of_quasipoly_gap_right,
    Q43_gap_right_k0_le_log2_of_pow_le,
    Q43_hrThreshold_of_quasipoly_gap_band_k,
    Q43_hrThreshold_of_quasipoly_gap_band_log2,
    Q43_hrThreshold_log2_bound,
    Q43_hrThreshold_of_flat_eval,
    Q43_log2_grid_size_eq_double_of_le_nk,
    Q43_grid_ratio_mono_on_gap_left,
    Q43_pow5_even_le_two_pow5_odd,
    Q43_gap_left_base_bound_of_k0,
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_left,
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_band,
    Q43_pow_succ_add_mul_le_succ_pow, Q43_pow5_sub_pow5_ge_five_pow4,
    Q43_log2_grid_size_eq_succ_of_bounds_self,
    Q43_log2_grid_size_eq_succ_of_ge_nk,
    Q43_grid_ratio_nk_succ_lower,
    Q43_gap_right_base_bound_of_c,
    Q43_gap_right_k0,
    Q43_three_mul_le_two_k_succ,
    Q43_gap_right_base_bound_of_k0,
    Q43_gap_right_n0,
    Q43_gap_right_k0_ge_one,
    Q43_gap_right_n0_ge_two,
    Q43_gap_right_apply_n0,
    Q43_grid_ratio_mono_on_gap_right,
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_right,
    Q43_nk_succ_le_three_pow);
    `scripts/toy_q43_gap_sqrt2.py`
  - `Success:` blocked by the entropy-stopper policy before the non-natural support predicate could be formalized (S366).
  - `Lens:` Barrier-driven design (natural-proofs barrier + entropy-stopper).
  - `Artifact:` Barrier.
  - `Update:` Entropy-stopper block recorded in `docs/q43_s366.md`; keeper plan is to reissue S366 once the score drops or pivot to a new idea.
  - `Use:` next: monitor `agent/logs/*` and wait for the entropy score to fall before re-running `Q43.S366-escape-natural-proof`, or craft S367 with new constraints.
  - `BarrierCheck:` see `docs/q43_s366.md`.
  - `InfoGain:` 0.
    Details: `docs/q43_s366.md`.

## Completed (archive)

- [X] **Q00 (Entropy Stopper v1 tooling):**
  closed: added stopper policy + entropy features + advice integration; run meta now embeds entropy decisions.
  `StepID:` Q00.S001-entropy-stopper-v1. `InfoGain:` 1. `NextStepID:` Q00.S002-entropy-tuning.
- [X] **Q44 (repo hygiene: remove legacy notebook checks):**
  closed: deleted `code/verify_checks.py`, `scripts/verify_notebook.py` now only performs structural checks,
  optional toy checks are launched via `--checks`. `StepID:` Q44.S1-drop-legacy-checks. `InfoGain:` 1.
- [X] **Q42 (flat local-EF(s): transfer HR t-evaluation -> Lemma 2.13):**
  closed: introduced cost-$t$ evaluation for flat local-EF(s) and showed that HR Lemma 2.13 carries over by replacing the depth parameter with cost (threshold $t\\le\\Theta(n/s)$); see `formal/Notes/TseitinLocalEF.lean` §16.162. `StepID:` Q42.S1-define-evaluation-flat. `InfoGain:` 2.
- [X] **Q41 (if Q39 is open: local extensions):**
  closed: (i) counterexample shows that "nested extension" without deploying support makes local-EF(s) trivial (Section 16.160);
  (ii) an analogue of HR Cor. 2.7 is proven in the flat model at $\\mathrm{supp}_s/\\mathrm{cost}_s$ (Section 16.161). `StepID:` Q41.S3-proof-cor27-analogue-flat. `InfoGain:` 2.
- [X] **Q40 (literary status Q39):**
  closed: in Hastad-Risse'22 Section 1.2 the exact quote "We do not know how to syntactically translate a Gaussian elimination step..." is recorded, with page (p. 4; PDF p. 6); see `formal/Notes/TseitinQ39.lean` §16.122. `StepID:` Q40.S1-quote-hr22-1.2. `InfoGain:` 1.
- [X] **Q38 (constants in depth threshold for Tseitin(Grid): compare Hastad'20 and GIRS'19):**
  closed: after recalculation (Section 16.117+Section 16.120), the comparison "59 vs upper constant" turned out to be an incorrect goal: the known polynomial size upper on the grid has a scale of $O(\\log n)$, and not $\\Theta(\\log n/\\log\\log n)$.
- [X] **Q37 (include a short summary of Tseitin(Grid) - current boundaries in the main text):**
  closed: in `docs/15_proof_complexity.md` now the wording is correct
  $\\Omega(\\log N/\\log\\log N)\\le d_{\\mathrm{poly}}(N)\\le O(\\log N)$; details: Section 16.92+Section 16.115+Section 16.116+Section 16.120.
- [X] **Q36 (reduce depth $d$ from GIRS'19 Thm. 19 to depth at 16.92/16.97 and rewrite in terms of $N$):**
  closed: rewrite in terms of $N$ done in `formal/Notes/TseitinCore.lean` Section 16.116 (and amended to remove the tight statement).
- [X] **Q35 (quantify the upper estimate of Thm. 19 (GIRS'19) and compare with 16.92):**
  closed: in `formal/Notes/TseitinCore.lean` Section 16.115+Section 16.120 the explicit upper $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ from Claim 28 is written out,
  and it is shown that it guarantees polynomial-size only for $d=\\Theta(\\log n)$ (and for $\\Theta(\\log n/\\log\\log n)$ - only quasi-poly).
- [X] **Q34 (explicit construction of $O(\\log n)$depth Frege refutation of Tseitin in the standard language):**
  closed: in `formal/Notes/TseitinCore.lean` Section 16.93 issued a self-sufficient output via Urquhart'87 (16.91) + Spira balancing (16.94)

  + linereplacement (16.113) + pproof of balancing equivalence (16.114).
- [X] **Q33 (Spira-balancing: where to get the p-dimensional Frege-output $A\\leftrightarrow A'$?):**
  closed: Buss'97, Proof (Sketch) to Thm. 3 (p. 8) directly notes the presence of polynomial-size Frege-evidence,
  verifying the correctness of the Spira translation (in particular, equivalence of the form $A\\leftrightarrow A'$);
  this is recorded in `formal/Notes/TseitinCore.lean` Section 16.114, and 16.94 are now strict through Section 16.113.
- [X] **Q32 (close "technical" part 16.94: line balancing in Frege):**
  closed: the scheme "output $A'$ from $A$ and $A\\leftrightarrow A'$" and the blow-up estimate are written in `formal/Notes/TseitinCore.lean` §16.113;
  The status of step 16.94 has been updated to "proven".
- [X] **Q31 (relink Section 16.110 to Section 16.112 and remove informality):**
  closed: Section 16.110 replaced $\\log n\\le\\log S$ with reference "see Section 16.112" and verified that there are no other uses of $n\\le S$
  (from now on only $\\log n\\le\\log S$ is used through Section 16.112).
- [X] **Q30 (justify step $\\log n\\le\\log S$ for Tseitin: $S\\ge |V(G)|$):**
  closed: for a connected $G$, removing any block $\\mathrm{PARITY}_{v,\\sigma(v)}$ makes $T(G,\\sigma)$ satisfiable (explicit spanning tree construction),
  this means that any resolutional refutation uses at least one initial clause from each block and $S\\ge |V(G)|$; see `formal/Notes/TseitinCore.lean` §16.112.
- [X] **Q29 (reduce AR'11 (2.15/2.17/2.18) into one "usable" remark):**
  closed: summary with explicit references and constants written to `formal/Notes/TseitinCore.lean` §16.111.
- [X] **Q28 (AR'11 Thm. 2.17: explicit dependence in $\\bigl(\\tilde\\ell(G)\\log S\\bigr)^{O(\\tilde\\ell(G)^2)}$):**
  closed: from the proof of Thm. 2.17 we can extract the explicit rough constant $c=6$ in
  $W\\le (C\\,\\tilde\\ell(G)\\log S)^{c\\tilde\\ell(G)^2}$; see `formal/Notes/TseitinCore.lean` §16.110.
- [X] **Q27 (AR'11 Thm. 2.15: explicit power in $\\ell(G)^{O(1)}$):**
  closed: from (5.4) and (5.6) in the proof of AR'11 Thm. 2.15 follows $W\\le O(\\ell(G)^7\\log S)$; see `formal/Notes/TseitinCore.lean` §16.109.
- [X] **Q26 (AR'11: planar graphs with bounded degree of faces  bounded cyclicity $\\ell(G)$):**
  closed: if $G$ is 2-edge-connected and admits a planar embedding, where each face has degree $\\le d$,
  then the boundaries of the faces provide coverage of the edges by cycles of length $\\le d$ and multiplicity $\\le 2$, which means $\\ell(G)\\le\\max\\{d,2\\}$; see `formal/Notes/TseitinCore.lean` §16.108.
- [X] **Q25 (Tseitin: $W(T(G,\\sigma)\\vdash\\bot)$ via $\\mathrm{cw}(G)$):**
  closed: from $\\tfrac18\\,\\mathrm{wb}(H_T)\\le W\\le 2\\,\\mathrm{wb}(H_T)$ (AR'11, Thm. 2.12 + Section 4) and
  $\\mathrm{wb}(H_T)=\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$ (Remark 2.11 + Section 16.105-16.106) we obtain
  $\\mathrm{cw}(G)/8\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{cw}(G)$; see `formal/Notes/TseitinCore.lean` §16.107.
- [X] **Q24 (hyperedge repetitions vs $\\mathrm{wb}$ in AR'11 Remark 2.11):**
  closed: in AR'11, the hypergraph $H_{T(G,\\sigma)}$ is a multi-$G^*$ (Def. 2.1 allows multiset), where $E(v)$ is repeated $2^{\\deg(v)-1}$ times (Remark 2.11),
  and for $G^*$ such repetitions do not change $\\mathrm{wb}$; see `formal/Notes/TseitinCore.lean` §16.106.
- [X] **Q23 (branch‑width $G^*$ vs carving width $\\mathrm{cw}(G)$):**
  closed: for the dual hypergraph $G^*$ (hyperedges are stars $E(v)$) branch-decomposition over hyperedges is equivalent to carving-decomposition of $G$ over vertices,
  and $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$; see `formal/Notes/TseitinCore.lean` §16.105.
- [X] **Q22 (constants in $\\Theta(\\cdot)$ from AR'11 Thm. 2.12):**
  closed: from AR'11 Prop. 4.3 and proofs of Lemma 4.4 (via Figure 3.1 / Lemma 3.1) we obtain explicit estimates
  $\\tfrac18\\,\\mathrm{wb}(T(G,\\sigma))\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{wb}(T(G,\\sigma))$;
  see `formal/Notes/TseitinCore.lean` Section 16.104 and
  `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [X] **Q21 (Tseitinwidth via branchwidth):**
  closed: Alekhnovich-Razborov (2011, Thm. 2.12) state
  $\\mathrm{wb}(T(G,\\sigma))=\\Theta(W(T(G,\\sigma)\\vdash\\bot))$, and Remark 2.11 specifies that the underlying hypergraph is $G^*$ (with repetitions);
  see `formal/Notes/TseitinCore.lean` Section 16.103 and `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [X] **Q20 (consistent with use of $w(G)$ in Cor. 34 / Section 16.98):**
  closed: Section 16.98 added explicit definition of $w(G):=W(T(G,\\varphi)\\vdash\\bot)-1$ and chain
  $n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log n)}$ via Harvey-Wood (2014, (2));
  see `formal/Notes/TseitinCore.lean` Section 16.102 and
  `../resources/downloads/harvey_wood_2014_treewidth_line_graphs.pdf`.
- [X] **Q19 (exact reference to $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ for Tseitinwidth):**
  closed: Galesi-Talebanfard-Toran (2018, ECCC TR18170) give Cor. 8:
  $W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{ec}(G)-1\\}$ and Cor. 16:
  $\\mathrm{ec}(G)=\\mathrm{tw}(L(G))+1$, whence $W=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}$ and $w(G)=W-1$.
  See `formal/Notes/TseitinCore.lean` Section 16.101 and `../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`.
- [X] **Q18 (connect carving width $W$ with $w(G)$ in Cor. 34):** closed: proven $\\mathrm{cw}(G)\\le \\mathrm{tw}(L(G))+1$;
  together with the formula for Tseitinwidth $w(G)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ (16.101) we obtain
  $\\mathrm{cw}(G)\\le w(G)+2$ and we can rewrite $n^{O(\\mathrm{cw}(G))}$ as $n^{O(w(G))}$; see `formal/Notes/TseitinCore.lean` §16.100.
- [X] **Q17 (Cor. 34: dependencies and "where exactly does it come from" treelike Res <= n^{O(w)}):** closed:
  The exact link for treelike upper bound is Beame-Beck-Impagliazzo (2016), Lemma 61 (via carving width),
  see `formal/Notes/TseitinCore.lean` Section 16.99 and
  `../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`.
- [X] **Q16 (Tseitin: bounded-depth Frege  treelike Resolution):** closed: exact formulation of Cor. 34:
  bounded-depth Fregeproof of size $S$  treelike Resolution of size $\\le 2^{\\mathrm{poly}(\\log S)}$
  (Galesi-Itsykson-Riazanov-Sofronova 2019, Cor. 34), see `formal/Notes/TseitinCore.lean` Section 16.98 and
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [X] **Q15 (narrow depthvssize gap for Tseitin):**
  closed: Thm fixed. 18/19 from GIRS'19 (2019, ECCC TR19069) as family bounds $2^{\\mathrm{tw}(G)^{\\Omega(1/d)}}$ and $2^{\\mathrm{tw}(G)^{O(1/d)}}\\cdot\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)$
  (in the original article $d$ is treated as a fixed depth; for growing $d$ the explicit dependence on $d$ is important, see Section 16.115-Section 16.121 and Q39).
  See `formal/Notes/TseitinCore.lean` Section 16.97 and `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [X] **Q14 (Fregedepth for Tseitin):** closed: polysize Frege refutation (Urquhart 1987; Section 16.91),
  bounded-depth lower bound on grid (Hastad 2020; Section 16.92), upper bound depth $O(\\log n)$ for boundeddegree
  (Hastad 2020 remark + Buss 1997/Spira translation; Section 16.93 and Section 16.95), and a reference to formulaic balancing (Bonet-Buss 2002; Section 16.94).
- [X] **Q13 (Frege/EF simulates XOR/Gauss):** in `formal/Notes/TseitinCore.lean` Section 16.88 added exact reference,
  that EF "easily simulates Gaussian elimination" (Bonet-Buss-Pitassi 2002, `../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7),
  which covers the folklore of the EFframework of XORsummation.
- [X] **Q12 (TseitinCNF vs PC at $\\mathrm{char}(F)\\ne 2$):** in `formal/Notes/TseitinCore.lean` §16.90
  shown: TseitinCNF (3CNF) and binomial Tseitin (Fourier/1base) pequivalent in degree in PC for $\\mathrm{char}(F)\\ne 2$,
  therefore degree/sizeLB (Razborov 2023, Thm. 6.8; Beame-Sabharwal 2000, Thm. 2.18) are transferred to TseitinCNF.
- [X] **Q11 (TseitinCNF vs PC over $\\mathbb F_2$):** in `formal/Notes/TseitinCore.lean` §16.89
  an explicit PC derivation of the linear equation of a vertex from 4 clauses and a final refutation of degree 3 and size $O(|V|)$ are given.
- [X] **Q10 (Tseitin vs EF/PC):** in `formal/Notes/TseitinCore.lean` Section 16.88 fixed: over fields of odd/zero characteristic, any PC-refutation $\\mathrm{Tseitin}(G_n)$ for bounded-degree expanders has degree $\\Omega(|V_n|)$ and, according to the degree->size connection, exponential size (Razborov 2023, Thm. 6.8 + paragraph after Thm. 6.9). Over $\\mathbb F_2$ degree 1 (sum of equations). The EFframework is also written there: XORequations are derived from 3CNF along the vertices, their XORsum gives $0=1$.
- [X] **Q9 (boundedocc Tseitinfamily):** in `formal/Notes/TseitinCore.lean` Section 16.87 fixed: explicit 3regular expander family (see `../resources/downloads/arora_barak.pdf`, Section 16.3, Remark 16.10)  $e(G)=\\Omega(|V|)$, which means 3CNF Tseitin from Section 16.85 has boundedocc = 8 and resolution size $2^{\\Omega(|V|)}$ according to Section 16.86.
- [X] **Q8 (Tseitin  resolution lower bounds):** extracted from `../resources/downloads/itsykson_oparin_2013_tseitin.pdf` (Cor. 1 + Thm. 1) and recorded as a **formally stated** step `formal/Notes/TseitinCore.lean` Section 16.86: for $\\deg(G)\\le k$ we have $W\\ge e(G)-1$ and $S\\ge 2^{(e(G)-k-1)^2/|E|}$, which means that on boundeddegree expanders the resolution is exponential.
- [X] **Q7 (Tseitin as candidate):** in `formal/Notes/TseitinCore.lean` Section 16.85 the definition of the XOR-system Tseitin($G,\\chi$) is given, unsatisfiability is proven for an odd sum of charges (parity invariant) and an explicit 3-CNF encoding for 3-regular graphs is written (size $4|V|$, bounded-occ = 8).
- [X] **Q6 (planar+occ for 15.7.4d):** proven Planar3SAT <=p Planar3SAT(<=4occ) (local split preserving planarity) in `formal/Notes/Encodings.lean` Section 16.84; fact added to Lemma 15.7.4d.
- [X] **Q5 (planar 3SAT blowup for 15.7.4d):** added estimate $|r(\\varphi)|=O(|\\varphi|^2)$ as a **formally stated** step `formal/Notes/Encodings.lean` Section 16.83 and 1-line remark in Lemma 15.7.4d.
- [X] **Q4b (canonization/ROABP barrier):** Lemma 15.7.4d now notes that the NP-hardness of 3SAT(<=4occ) follows from explicit linear reduction `formal/Notes/Encodings.lean` Section 16.81-16.82 (barrier check: r applicable; NP/alg not relevant).
- [X] **Q4a (canonization/ROABP barrier):** added **formally stated** steps `formal/Notes/Encodings.lean` Section 16.81-16.82: Tovey-splitting gives (O3, $L\\le 3$)-SAT with linear blow-up, and 2-clauses are eliminated by padding-replacement $(x\\vee\\neg y)\\mapsto(x\\vee x\\vee\\neg y)$, getting 3-SAT with the restriction "each variable <=4 occurrences".
- [X] **Q1 (Pich-Santhanam 2023):** formal formula fixed `tt(f_n,s,t)`, equivalence and place of use (see `docs/15_proof_complexity.md`).
- [X] **Q2 (EF+assumptions  P=NP):** (H1$_\\Pi$)/(H2$_\\Pi$) are written as $\\forall\\Pi^b_1$-formulas and hidden gains (a.e.-hardness and fixed $R$) are marked; see `docs/15_proof_complexity.md`.
- [X] **Q3 (minimal non-relativizing step):** added Lemma 15.7.3 (PIT axioms  EF p-simulates IPS) with sketch and barrier check; see `docs/15_proof_complexity.md`.
- [X] **Q3a (PIT  IPS/EF):** in Lemma 15.7.3c added an explicit linear calculation of the size of the CNF->3CNF reduction (<=$L$ clauses and <=$3L$ literals for $L$ literals of the original CNF); see also `formal/Notes/Encodings.lean` §16.78.
- [X] **Q4 (canonization/ROABP barrier):** added Lemma 15.7.4 (weak barrier for CNF class); see `docs/15_proof_complexity.md`.
- [X] **Q2a (EF+assumptions  P=NP):** added a remark next to Lemma 15.7.2b: the quantifier $C\\le m(s)$ is only a bounded constraint on the length of the code (padding), all meaningful restrictions go through $\\mathrm{Valid}_s(C)$; see also `formal/Notes/Encodings.lean` §16.79.
- [X] **Q1a (Pich-Santhanam 2023):** connects the counter size estimate from Lemma 15.7.1d with 3CNFcoding via Tseitin: added remark next to 15.7.1d and **formally stated** step `formal/Notes/Encodings.lean` §16.80.
