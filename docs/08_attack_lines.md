## 8. Lines of attack (select one and deepen)

Work queue: `open_questions.md`.

1) **Circuit complexity:** lower bounds on the size/depth of circuits for explicit functions (SAT/CLIQUE, etc.).
2) **Proof complexity:** lower bounds for the length of evidence (connection with NP vs coNP).
3) **Hardness vs Randomness / de-randomization:** equivalence between lower bounds and pseudo-randomness.
4) **Algebraic complexity (VP vs VNP) and IPS:** algebraic schemes/certificates;
   superpolynomial lower bounds IPS  VP=VNP (Section 15.7; known
   estimates - for limited subsystems).
Status: VP=VNP and IPSlower grades are open; more details section 9.
Briefly: VP are families of polynomials computable by polynomial algebraic
diagrams; VNP - "NP-analogs" according to Valiant (polynomial sums of VP).
Reminder: IPS is an algebraic proof system, while EF is a Boolean proof system (Section 15.7).
Review: Blaser-Ikenmeyer 2025 (`../resources/downloads/blaser_ikenmeyer_2025_gct_intro.pdf`).
Original VP/VNP source: Valiant 1979 (Burgisser 2024,
`../resources/downloads/burgisser_2024_valiant_overview.pdf`).
**Selected line (current): proof complexity.** The goal is to understand where exactly
standard systems of evidence "resist" and how this relates to
$\mathrm{NP}$ vs $\mathrm{coNP}$.
Specific open target: show that
$\mathrm{EF}+tt(h_{0,n},2^{n/4},t(n))$ is not p-bounded (Section 15.7).

Minimum goal (done in section 15): fix definitions
(proof system/resolution), write out $\mathrm{PHP}$ and check on small $n$,
**completely prove** the exponential lower bound for the resolution on
$\mathrm{PHP}$ (Theorem 15.2).

Next step:
- capture minimal facts about strong systems (PHP is easy in Frege/CP,
  difficult in AC0Frege) and then focus on the EFlower bounds from Section 15.7.

**Map of implications (neat).**
- Polynomial bounded proof system for TAUT  $\mathrm{NP}=\mathrm{coNP}$
  (Lemma 15.1).
- To output $\mathrm{P}\ne\mathrm{NP}$, $\mathrm{NP}\ne\mathrm{coNP}$ is sufficient;
  equivalent: every proof system has tautologies with superpolynomial proofs.
- If there is a p-optimal system and superpolynomials have been proven for it
  lower bounds, then $\mathrm{NP}\ne\mathrm{coNP}$ (the existence of a p-optimal is open).
- Conditional results (Pich-Santhanam 2023): EF-lower estimates +
  $\mathrm{S}^1_2$-formalizable reductions  $\mathrm{P}\ne\mathrm{NP}$.
- Uneven vs uniform: $\mathrm{SIZE}$/$\mathrm{P/poly}$ stronger
  $\mathrm{Time}[n^k]/u(n)$; a smaller $u(n)$ enhances the output; Cor. 2 gives
  uniform lower bounds for fixed $u(n)$ (Section 15.7).
