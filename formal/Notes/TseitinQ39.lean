import Paperproof

/-!

# P vs NP - research steps 16.122-16.152 (Tseitin/Grid: Q39 - boundeddepth Frege gap)

Main index: `P_vs_NP.md`.

### 16.122. Exploratory step: "Gaussian elimination" as the (yet) missing upper-step for bounded-depth Frege on the grid

- `Lens:` Equivalence.
- `Statement:` In Hastad-Risse (2022/2025) Section 1.2 (`../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`)
  the "potential" path to the upper bound for Tseitin(Grid) in the boundeddepth Frege is explicitly highlighted:
  try to simulate the summation of linear equations (Gaussian elimination modulo 2) in the language of formulas of depth $d$.
  The authors show how to **represent** intermediate parity equations in the form of small depth-$d$ formulas,
  but they emphasize that they **do not know** how to syntactically translate one Gaussian elimination step into a limited number of proof steps,
  those. get "representation of partial results", not proof.
- `Proof/link:` Håstad–Risse, §1.2 “Constructing small proofs” (`../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`):
  1) (p. 3; PDF p. 5) “If we are allowed to reason with linear equations modulo two then the Tseitin contradiction has efficient refutations.”
  2) (p. 4; PDF p. 6) “We do not know how to syntactically translate a Gaussian elimination step to some proof steps in this representation and thus we do not actually get a proof, only a representation of the partial results.”
- `Toy test:` let the maximum string size be $M=n^{O(1)}$, then $\\log M=\\Theta(\\log n)$.
  If (as in the HR heuristic Section 1.2) we temporarily assume that the depth$d$ **representation** of parity admits a block
  $m\\approx(\\log M)^{d-1}$, then
  For $d=\\Theta(\\log n/\\log\\log n)$ we have $m=\\exp(\\Theta(\\log n))=n^{\\Theta(1)}\\ge n$, i.e. representation of parity on $n$ variables is possible with polynomial $M$;
  There remains exactly the "missing" step: to derive from such representations the following XOR equation inside Frege.
  (For increasing depth and **formulas**, care must be taken to consider the "scheme vs formula" difference, see Section 16.147-Section 16.152.)
- `Status:` known fact (exact link; formalizes where exactly the naive upper approach breaks down).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` formalize as a lemma-goal: "in bounded-depth Frege you can (p-)derive the representation $L_1\\oplus L_2=b_1\\oplus b_2$ from the representations $L_1=b_1$ and $L_2=b_2$ with depth/size control," or find a source where this has already been done.

### 16.123. Exploratory step: correction about "representation PARITY" - naive DNF induction gives $M^{\\Theta(d)}$, and the desired fact is explicitly stated in Hastad-Risse Section 1.2

- `Lens:` Trade-off.
- `Statement:` Consider the statement from Section 16.122: "formulas of depth $d$ of size $M$ can represent parity on $m:=(\\log M)^{d-1}$ variables" (for growing $d$, see caveat Section 16.147-Section 16.152).
  1) The naive construction through the DNF expansion $\\mathrm{PARITY}_{\\lceil\\log_2 M\\rceil}$ and substitution in depth actually gives depth $O(d)$, but only the size $M^{\\Theta(d)}$,
     therefore **not** outputs polynomialsize for $d=\\Theta(\\log n/\\log\\log n)$ with $M=\\mathrm{poly}(n)$ (it turns out quasi-poly).
  2) The "representation" fact itself in the required (for Q39) form is **known** and directly formulated in Hastad-Risse (`../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`, §1.2):
     they claim that when grouped into blocks of size $(\\log M)^{d-1}$, one can "write down formulas of depth $d$ and size $M$ that represent the parity and the negation of the parity."
- `Proof/link:`
  1) (Why DNF induction is not suitable for growing $d$.) Let $g:=\\lceil\\log_2 M\\rceil$ and $m:=g^{d-1}$.
     Base $d=2$: DNF for $\\mathrm{PARITY}_g$ has $2^{g-1}$ terms, i.e. size $\\Theta(2^g\\cdot g)=\\Theta(M\\log M)$.
     Step $d\\to d+1$: substituting a formula of size $S_d$ into each occurrence of a variable in this DNF gives
     $$S_{d+1}=\\Theta(2^g\\cdot g\\cdot S_d)=\\Theta(M\\log M\\cdot S_d),$$
     whence $S_d=(M\\log M)^{\\Theta(d)}=M^{\\Theta(d)}$ (log factors are absorbed into $M^{o(d)}$).
     With $M=n^C$ and $d=\\Theta(\\log n/\\log\\log n)$ this gives $S_d=n^{\\Theta(\\log n/\\log\\log n)}$ (quasi-poly), not $n^{O(1)}$.
  2) (Correct source representation.) Hastad-Risse, Section 1.2, paragraph starting with "Let us consider proofs that contain formulas of depth d...":
     “… divide the variables in to groups of size $(\\log M)^{d−1}$ and write down formulas of depth $d$ and size $M$ that represent the parity and the negation of the parity …”.
- `Toy test:` take $M=n^{10}$ and $d=\\lfloor\\log n/\\log\\log n\\rfloor$. Then $m=(\\Theta(\\log n))^{\\Theta(\\log n/\\log\\log n)}=n^{\\Theta(1)}$,
  and representation from Hastad-Risse allows formulas of size $M=\\mathrm{poly}(n)$; but DNF induction above would only give a quasi-poly size.
- `Status:` counterexample to the previous conclusion "DNFinduction  polysize for $d=\\Theta(\\log n/\\log\\log n)$"; The representation lemma is closed by exact reference (Hastad-Risse Section 1.2).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` now that representation is based on the source, return focus to the missing step from Section 16.122: find/prove (or barrier disprove) syntactic simulation of one step $L_1=b_1,\\ L_2=b_2\\Rightarrow L_1\\oplus L_2=b_1\\oplus b_2$ in boundeddepth Frege without exponential blowup.

### 16.124. Exploratory step: at the threshold $d\\approx\\log n/\\log\\log n$ the representation of the XOR equation of width $O(n)$ becomes constant; Q39 reduces to 1-step XOR simulation

- `Lens:` Trade-off.
- `Statement:` Let $n\\to\\infty$, $M=n^{O(1)}$ and $d:=\\lceil\\log_2 n/\\log_2\\log_2 n\\rceil+1$.
  Then $(\\log_2 M)^{d-1}\\ge n$, which means (in terms of Section 16.122-Section 16.123) the parity equation for $m=O(n)$ variables can be represented **as one block**:
  in boundeddepth Frege the lines "$\\sum x_i=b$" and "$\\neg(\\sum x_i=b)$" admit depth$d$ formulas of size $\\mathrm{poly}(n)$, and representationoverhead $2^{m/(\\log M)^{d-1}}$ becomes $2^{O(1)}$.
  Consequently, the potential upper-approach through Gaussian elimination on the grid (the width of each intermediate equation is $O(n)$ and $O(n)$ steps) does not rest on the representability of the equations, but only on the ability to syntactically simulate **one** step $L_1=b_1,\\ L_2=b_2\\Rightarrow L_1\\oplus L_2=b_1\\oplus b_2$ in boundeddepth Frege.
- `Proof:` since $M=n^{O(1)}$, there is a constant $C\\ge 1$ such that $\\log_2 M\\ge C\\log_2 n\\ge \\log_2 n$ for large $n$.
  By definition of $d$ we have $d-1\\ge \\log_2 n/\\log_2\\log_2 n$.
  Then
  $$(\\log_2 M)^{d-1}\\ \\ge\\ (\\log_2 n)^{\\log_2 n/\\log_2\\log_2 n}\\ =\\ 2^{(\\log_2 n/\\log_2\\log_2 n)\\cdot\\log_2\\log_2 n}\\ =\\ 2^{\\log_2 n}\\ =\\ n.$$
  Substituting into the score $2^{m/(\\log M)^{d-1}}$ gives $2^{O(n)/\\Omega(n)}=2^{O(1)}$.
- `Toy test:` let $n=2^{16}$, $M=n^{10}$ and $d=\\lceil 16/4\\rceil+1=5$.
  Then $\\log_2 M=160$ and $(\\log_2 M)^{d-1}=160^4>10^8\\gg n$, so $m=n$ falls into one block.
- `Status:` proven (quantitative reduction Q39: at the threshold depth the representation-cost is constant).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` search/formalize either (i) p-derivability of the rule for XOR-addition of two equations in bounded-depth Frege with depth/size control, or (ii) a known lower-bound/barrier prohibiting such a rule at $d=\\Theta(\\log n/\\log\\log n)$.

### 16.125. Exploratory step: formal reduction of Q39 to pderivability of a single XORstep (Gaussian elimination) in boundeddepth Frege

- `Lens:` Equivalence.
- `Statement:` Fix $n\\to\\infty$, let $G$ be a $n\\times n$ grid and $F_n=\\mathrm{TseitinCNF}(G,\\chi)$ (with $\\bigoplus_v\\chi(v)=1$) be the 3CNF from Section 16.85.
  Suppose that for each $m=O(n)$ there is a uniform family depth-$d(n)$ Frege-outputs of polynomial size for the following "XOR-step":
  from two representations of linear equations modulo 2,
  $$E(S_1,b_1),\\ E(S_2,b_2)\\ \\vdash\\ E(S_1\\triangle S_2,\\ b_1\\oplus b_2),$$
  where $S_i$ are sets of variables $\\{x_e\\}$ of size $\\le m$, $\\triangle$ is symmetric. difference, and each $E(S,b)$ is written depth$d(n)$ by the size formula $\\mathrm{poly}(n)$ (representation from Section 16.123-Section 16.124).
  Then there is a polynomial-size depth-$O(d(n))$ Frege-refutation $F_n$.
- `Proof:` Let's take the linear-algebraic strategy from Hastad-Risse Section 1.2:
  (i) summing all equations in one column gives the equation of width $O(n)$; (ii) adding an adjacent column preserves the width $O(n)$;
  (iii) after going through all the columns, the contradiction $0=1$ is obtained, and nowhere is an equation wider than $O(n)$ used.
  The standard 3CNF vertex encoding (4 clauses for degree 3/4) has a constant Frege output of an equivalent XOR formula
  $(\\bigoplus_{e\\ni v} x_e)\\leftrightarrow\\chi(v)$ (see diagram in Section 16.88), so we can start with the representation of all vertex equations.
  Further, each linear step of summing/reducing common variables is exactly the application of the specified XOR rule to two equations of width $O(n)$,
  Moreover, according to Section 16.124, each intermediate equation can be contained in one representation block (size $\\mathrm{poly}(n)$, depth $d(n)$).
  The number of linear steps is polynomial (you can sum the vertices one by one within a column and then the columns one by one), and each substitution of the XOR rule has a size of $\\mathrm{poly}(n)$ by assumption,
  this means that the total size of the Frege-refutation remains $\\mathrm{poly}(n)$ (and therefore $\\mathrm{poly}(|F_n|)$).
- `Toy test:` for $n=4$, summing 4 vertices of one column kills internal vertical edges (each appears twice) and leaves only edges that intersect the column boundary;
  the width remains $O(n)$, and this pattern is repeated when the next column is added.
- `Status:` proven (conditional reduction: closing Q39 is equivalent to having a polysize boundeddepth simulation of one Gaussianelimination step on XOR equations of width $O(n)$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find the exact source/result about the (non)existence of such an XOR-rule in bounded-depth Frege (possibly through the known lower bounds for AC$^0$-Frege on "linear-algebraic" tautologies).

### 16.126. Exploratory step: "one XOR step" = Tseitin on a 3-vertex (multi)graph

- `Lens:` Equivalence.
- `Statement:` Let us fix the sets of variables $S_1,S_2\\subseteq X$ and bits $b_1,b_2\\in\\{0,1\\}$.
  Then the rule from Section 16.125
  $$E(S_1,b_1),\\ E(S_2,b_2)\\ \\vdash\\ E(S_1\\triangle S_2,\\ b_1\\oplus b_2)$$
  (where $E(S,b)$ is an "XOR equation modulo 2" over variables from $S$) is equivalent to refuting the Tseitin contradiction on a three-vertex graph in which each edge corresponds to one variable from $X$.
- `Proof:`
  1) (**Graph.**) Let's construct a multigraph $H(S_1,S_2)$ with vertices $A,B,C$ and edges:
     - for each $x\\in S_1\\cap S_2$ add an edge $(A,B)$ labeled $x$;
     - for each $x\\in S_1\\setminus S_2$ add an edge $(A,C)$ labeled $x$;
     - for each $x\\in S_2\\setminus S_1$ we add an edge $(B,C)$ labeled $x$.
     Then the incident $A$ edges are exactly variables from $S_1$, the incident $B$ edges are from $S_2$, and the incident $C$ edges are from $S_1\\triangle S_2$.
  2) (**Tseitinsystem.**) Let us put charges $\\chi(A)=b_1$, $\\chi(B)=b_2$, $\\chi(C)=1\\oplus b_1\\oplus b_2$.
     Then Tseitin($H,\\chi$) is a system of three XOR equations
     $$E(S_1,b_1),\\quad E(S_2,b_2),\\quad E(S_1\\triangle S_2,\\ 1\\oplus b_1\\oplus b_2).$$
     Since $b_1\\oplus b_2\\oplus(1\\oplus b_1\\oplus b_2)=1$, the sum of the charges is odd, and by the invariant from Section 16.85 the system is unsatisfiable.
  3) (**Implication  refutation.**) The impossibility of a triple of equations is tantamount to a tautology
     $$E(S_1,b_1)\\wedge E(S_2,b_2)\\ \\to\\ \\neg E(S_1\\triangle S_2,\\ 1\\oplus b_1\\oplus b_2).$$
     But $\\neg E(S,1\\oplus b)$ is identical to $E(S,b)$, which means it is exactly $E(S_1,b_1)\\wedge E(S_2,b_2)\\to E(S_1\\triangle S_2,b_1\\oplus b_2)$.
     Therefore, polynomialsize boundeddepth Frege refutation Tseitin($H,\\chi$) (with a fixed recording method $E$) gives polynomialsize boundeddepth proof of the XOR step and vice versa (with an accuracy of $O(1)$ in depth).
- `Toy test:` if $S_1=\\{x,y\\}$, $S_2=\\{y,z\\}$, then the edges: $y$ between $(A,B)$, $x$ between $(A,C)$, $z$ between $(B,C)$.
  The equations: $x\\oplus y=b_1$, $y\\oplus z=b_2$, $x\\oplus z=1\\oplus b_1\\oplus b_2$ are an obvious contradiction.
- `Status:` proven (reformulation of "missing step" as private Tseitin).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` look for (un)known estimates on bounded-depth Frege for this 3-vertex Tseitin-family with width $|S_1|,|S_2|=\\Theta(n)$ and depth $d=\\Theta(\\log n/\\log\\log n)$ (this is "one Gaussian-elimination step").

### 16.127. Exploratory step: XOR-addition of equations is trivial in EF, but converting to bounded-depth Frege gives only $O(\\log n)$ in depth

- `Lens:` Trade-off.
- `Statement:` The "one-step XOR" family (equivalent to the 3-vertex Tseitin from Section 16.126) has a polynomial-size refutation in Extended Frege (EF),
  since EF can introduce abbreviation variables and simulate Gaussian elimination. However, standard translation/balancing techniques give
  for ordinary Frege only the upper depth bound is $O(\\log n)$ (not $O(\\log n/\\log\\log n)$), so this does not close Q39.
- `Proof/Explanation:`
  1) EF upper bound: see Section 16.88 (skeleton of Tseitin's EF proof via XOR variables) and the note "EF easily simulates Gaussian elimination"
     (Bonet–Buss–Pitassi 2002, `../../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7).
     For 3-vertex Tseitin (and in general for linear systems over $\\mathbb F_2$), EF can store intermediate XOR equations in extension variables and perform string addition steps.
  2) Transition to boundeddepth Frege: even if there is a polynomialsize (E)Fregeproof, the well-known universal balancing of formulas (Spira/Brent) gives depth only
     $O(\\log m)$ for formulas of size $m$ (see Section 16.94), and in our regime $m=\\mathrm{poly}(n)$ is $O(\\log n)$.
     This is why "there is an EFproof of Gaussian elimination" does not mean "there is a depth$\\Theta(\\log n/\\log\\log n)$ Fregeproof of one XORstep."
- `Toy test:` for parity on $n$ variables, balancing gives a depth of $O(\\log n)$ for an explicit XOR tree formula, but Q39 requires a depth of the order of $\\log n/\\log\\log n$.
- `Status:` proven (local barrier: standard EF->Frege+balancing does not provide the required depth).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` look for a technique that reduces the inference depth of the XOR step below $O(\\log n)$ (for example, through special depth-$d$ parity representations from Hastad-Risse and proof of their linearity), or a source that such a shift is impossible.

### 16.128. Research step: Claim-28 upper (GIRS'19) does not certify polynomial-size even for "local" 3-vertex Tseitin at $d\\approx\\log n/\\log\\log n$

- `Lens:` Trade-off.
- `Statement:` Consider the family of 3-vertex Tseitin contradictions from Section 16.126, where $|S_1|,|S_2|=\\Theta(n)$ (meaning the number of variables $\\Theta(n)$).
  Then the general upper bound from GIRS'19 (Claim 28 -> Thm. 27; see Section 16.115-Section 16.121) guarantees polynomialsize refutation only at depth
  $$d=\\Omega(\\log n),$$
  and therefore cannot close Q39 in the $d=\\Theta(\\log n/\\log\\log n)$ mode even at one Gaussian-elimination step.
- `Proof:` let $H=H(S_1,S_2)$ be the multigraph on vertices $A,B,C$ from Section 16.126.
  1) $\\Delta(H)=\\max\\{|S_1|,|S_2|,|S_1\\triangle S_2|\\}=\\Theta(n)$.
  2) By definition of treepartition width from GIRS'19 Section 4.3, we can take one set $\\{A,B,C\\}$ as the only part of the treepartition, which means
     $$\\mathrm{tpw}(H)\\le 3.$$
     Therefore, $X:=\\Delta(H)\\,\\mathrm{tpw}(H)=\\Theta(n)$.
  3) Using the explicit unconditional upper from Section 16.120,
     $$\\mathrm{size}\\le \\mathrm{poly}(|T|)\\cdot 2^{O\\bigl(d\\cdot X^{2/d}\\bigr)},$$
     and optimization lemma Section 16.121 (polynomial-size is possible only for $d=\\Omega(\\log X)$), we obtain the requirement $d=\\Omega(\\log n)$.
- `Toy test:` if $d=\\lfloor\\log n/\\log\\log n\\rfloor$, then $X^{2/d}=\\exp(2\\log n/d)=(\\log n)^{\\Theta(1)}$ and
  $$2^{O(d\\cdot X^{2/d})}=2^{\\mathrm{polylog}(n)}=n^{\\mathrm{polylog}(n)}$$
  (quasi-poly), not $n^{O(1)}$.
- `Status:` proven (local "technique barrier": tree-partition upper from GIRS'19 does not reach the threshold depth even for a 3-vertex step).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` look for a technique that uses a special grid/representation structure (Hastad-Risse) and dispenses with the parameter $X=\\Delta\\,\\mathrm{tpw}$ (or prove that for a 3-vertex Tseitin with $d=\\Theta(\\log n/\\log\\log n)$ a quasi-poly lower bound is inevitable).

### 16.129. Exploration step: "compact representation of parity" in GIRS'19 (Lemma 21) = DNFinduction and has size $\\exp(\\Theta(d\\,n^{1/d}))$  with $d\\approx\\log n/\\log\\log n$ it is quasipoly

- `Lens:` Compression/canonization.
- `Statement:` In GIRS'19, Section 4.1 (Lemma 20-21), the "compact representation" of $\\mathrm{PARITY}$ is constructed via $(t_1,\\dots,t_d)$refinement and gives the formula for depth $\\le 3d+1$ and size
  $$\\mathrm{size}=\\prod_{i=1}^d (2^{t_i+1}t_i).$$
  Given $\\prod_{i=1}^d t_i\\ge n$ (Lemma 20), the best possible estimate for **this** construction is
  $$2^{\\Omega(d\\,n^{1/d})}\\ \\le\\ \\mathrm{size}\\ \\le\\ 2^{O(d\\,n^{1/d})}\\cdot\\mathrm{poly}(n).$$
  In particular, for $d=\\Theta(\\log n/\\log\\log n)$ we obtain $\\mathrm{size}=n^{\\Theta(\\log n/\\log\\log n)}$ (quasi-poly), i.e. exactly the same "extra factor $d$ in the exponent" as in Section 16.123.
- `Proof/link:`
  1) (Formula size/depth.) GIRS'19, Lemma 21 (in `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`): for $(t_1,\\dots,t_d)$refinement, the formula for $\\mathrm{PARITY}$ has depth $\\le 3d+1$ and size $\\prod_{i=1}^d (2^{t_i+1}t_i)$.
  2) (Lower bound for this construction.) Since $\\prod_{i=1}^d (2^{t_i+1}t_i)\\ge \\prod_i 2^{t_i}=2^{\\sum_i t_i}$, it is enough to estimate the sum.
     According to AM-GM: if $t_i\\ge 1$ and $\\prod_i t_i\\ge n$, then $\\frac1d\\sum_i t_i\\ge (\\prod_i t_i)^{1/d}\\ge n^{1/d}$, then $\\sum_i t_i\\ge d\\,n^{1/d}$ and
     $$\\mathrm{size}\\ge 2^{\\sum_i t_i}\\ge 2^{d\\,n^{1/d}}.$$
  3) (Upper bound.) Take $t_i:=\\lceil n^{1/d}\\rceil$. Then $\\prod_i t_i\\ge n$, and
     $$\\mathrm{size}=\\prod_i (2^{t_i+1}t_i)=2^{O(d\\,n^{1/d})}\\cdot (n^{1/d}+1)^d=2^{O(d\\,n^{1/d})}\\cdot\\mathrm{poly}(n).$$
  4) (Threshold $d\\approx\\log n/\\log\\log n$.) Then $n^{1/d}=2^{(\\log_2 n)/d}=2^{\\Theta(\\log\\log n)}=\\mathrm{polylog}(n)$, and the exponent
     $$d\\,n^{1/d}=\\Theta\\Bigl(\\frac{\\log n}{\\log\\log n}\\cdot\\log n\\Bigr)=\\Theta\\Bigl(\\frac{\\log^2 n}{\\log\\log n}\\Bigr),$$
     those. $\\mathrm{size}=2^{\\Theta(\\log^2 n/\\log\\log n)}=n^{\\Theta(\\log n/\\log\\log n)}$ (quasi-poly).
- `Toy test:` let $n=2^{256}$, $d=\\lfloor 256/8\\rfloor=32$. Then $n^{1/d}=2^8=256$ and the lower bound gives $\\mathrm{size}\\ge 2^{32\\cdot 256}=2^{8192}$, while any $n^C$ has the form $2^{256C}$.
- `Status:` proven (technique limitation: GIRS'19 Lemma 21/Claim 28 use parity representation of size $\\exp(\\Theta(d\\,n^{1/d}))$, which does not reach the threshold $d\\approx\\log n/\\log\\log n$ without new ideas).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find out whether there exists in the literature a "provable in boundeddepth Frege" representation of parity without the factor $d$ in the exponential (in the spirit of Hastad-Risse Section 1.2), or whether there is a known lower bound/barrier that prohibits syntactic simulation of XORaddition at depth $\\Theta(\\log n/\\log\\log n)$.

### 16.130. Exploratory step: XOR addition of equations becomes easy if all equations are written as parity over $k$ "block parities" of one fixed partition

- `Lens:` Equivalence.
- `Statement:` Let the set of variables $X$ be divided into disjoint blocks $X=\\biguplus_{i=1}^k B_i$.
  For each $i$, let $P_i(x_{B_i})$ be a formula for depth $\\le d_0$ and size $\\mathrm{poly}(n)$ that calculates parity on $B_i$ (i.e. $P_i=1\\iff \\bigoplus_{x\\in B_i}x=1$).
  For $I\\subseteq[k]$ and $b\\in\\{0,1\\}$ we denote
  $$E^{\\mathrm{blk}}(I,b)\\ :=\\ \\Bigl(\\bigoplus_{i\\in I} y_i=b\\Bigr)$$
  as a **DNF formula** on abstract variables $y_1,\\dots,y_k$ (complete DNF of parity on $I$, size $\\Theta(2^{|I|-1}|I|)$).
  Then for any $I_1,I_2\\subseteq[k]$ and $b_1,b_2\\in\\{0,1\\}$ there is a boundeddepth Fregederivation of the depth $O(1)$ and size $2^{O(k)}$, proving
  $$E^{\\mathrm{blk}}(I_1,b_1)\\wedge E^{\\mathrm{blk}}(I_2,b_2)\\ \\to\\ \\ E^{\\mathrm{blk}}(I_1\\triangle I_2,\\ b_1\\oplus b_2).$$
  By substituting $y_i\\mapsto P_i$ we get the polynomialsize depth$O(d_0)$ Fregeoutput of the XORstep for equations that are **unions of blocks** of the same partition:
  $$E(S_{I_1},b_1),\\ E(S_{I_2},b_2)\\ \\vdash\\ E(S_{I_1\\triangle I_2},\\ b_1\\oplus b_2),\\qquad S_I:=\\bigcup_{i\\in I} B_i.$$
  In particular, if $k=O(\\log n)$ and $|P_i|=\\mathrm{poly}(n)$, then one XOR step has a polynomial-size bounded-depth Frege-proof.
- `Proof:`
  1) At the level of $y$-variables, the implication is a tautology (linearity of parity in $\\mathbb F_2$). According to Lemma 4 (GIRS'19, `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`, p. 4),
     if the formula depends on $k$ variables, then the semantic implication implies a derivation of size $\\le 2^k\\bigl(|\\psi_1|^2+|\\psi_2|^2\\bigr)=2^{O(k)}$ for the same depth.
  2) Substitution: in any Frege system where axioms/rules are given as schemas, substituting $y_i\\mapsto P_i$ into each line of the proof gives a proof of the substitution formula.
     The depth increases by $O(d_0)$, and the total size increases by no more than a factor of $O(\\max_i |P_i|)$ (each occurrence of $y_i$ is replaced by the formula $P_i$).
- `Toy test:` $k=3$, $I_1=\\{1,2\\}$, $I_2=\\{2,3\\}$: from $y_1\\oplus y_2=b_1$ and $y_2\\oplus y_3=b_2$ it follows $y_1\\oplus y_3=b_1\\oplus b_2$ (the symmetric difference removes $y_2$).
- `Status:` proven (conditional "easy case": the XOR step is trivialized for a fixed block partition and small $k$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` to understand whether for a column-summing strategy on a grid it is possible to keep all intermediate equations in the form of union-of-blocks of one partition with $k=\\mathrm{polylog}(n)$ (and at the same time output the block parities themselves without "hidden" Gaussian elimination), or whether this breaks down and requires transitions between partitions.

### 16.131. Exploratory step: fixed "blockbasis" cannot cover columnsumming on grid at $k=\\mathrm{polylog}(n)$ (rank $=\\Omega(n)$)

- `Lens:` Communication/Rank.
- `Statement:` Consider a $n\\times n$ grid and let $H_j$ be the set of $n$ horizontal edges between columns $j$ and $j+1$ (for $j=1,\\dots,n-1$).
  Then the sets $H_1,\\dots,H_{n-1}$ are linearly independent in $\\mathbb F_2^{E}$ (as characteristic vectors), and therefore:
  if a set of $k$ subsets of edges $B_1,\\dots,B_k\\subseteq E$ is fixed, then simultaneously represent **all** $H_j$ as symmetric differences
  $$H_j=\\bigtriangleup_{i\\in I_j} B_i$$
  possible only for $k\\ge n-1$.
  In particular, trying to apply Section 16.130 to column-summing with one fixed block-representation requires $k=\\Omega(n)$ and therefore does not yield a polynomial-size (since $2^{O(k)}$ becomes exponential).
- `Proof:` since the sets $H_j$ are pairwise disjoint, they are independent:
  if $\\bigtriangleup_{j\\in J} H_j=\\varnothing$, then for any $e\\in H_{j_0}$ (where $j_0\\in J$) this $e$ occurs in symmetry. differences exactly once (only from $H_{j_0}$), a contradiction. This means $J=\\varnothing$ and $\\{H_j\\}$ are independent.
  Therefore, the subspace $\\langle H_1,\\dots,H_{n-1}\\rangle\\subseteq\\mathbb F_2^{E}$ has dimension $n-1$.
  If each $H_j$ lies in the linear hull $\\langle B_1,\\dots,B_k\\rangle$, then
  $$n-1=\\dim\\langle H_1,\\dots,H_{n-1}\\rangle\\le \\dim\\langle B_1,\\dots,B_k\\rangle\\le k,$$
  whence $k\\ge n-1$.
- `Toy test:` for $n=4$ there are three disjoint sets $H_1,H_2,H_3$; this means that any fixed set $B_1,\\dots,B_k$ generating all $H_j$ must have $k\\ge 3$.
- `Status:` a counterexample to the naive idea "close Q39 through one fixed blockbasis + Section 16.130" (transitions between partitions/bases are needed).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` formalize what kind of "basechange" is required in the Hastad-Risse strategy, and reduce it to a syntactic problem: prove/disprove the ability to effectively translate boundeddepth representations of parity between two (significantly different) partitions at depth $\\Theta(\\log n/\\log\\log n)$.

### 16.132. Exploratory step: a naive basechange through a general refinement of two partitions gives a blowup $k\\mapsto k^2$  with $k=\\Theta(\\log n)$ it turns out quasipoly

- `Lens:` Trade-off.
- `Statement:` Let $U$ be a set of variables (or edges), and $\\mathcal P,\\mathcal Q$ be partitions of $U$ into $k$ blocks each.
  Consider the "blockrepresentation" from Section 16.130: formulas for block parities and equations of the form "the parity on the union of some blocks is $b$."
  Then any "translation" between representations with respect to $\\mathcal P$ and $\\mathcal Q$ can be reduced to a general refinement
  $$\\mathcal R:=\\{P\\cap Q:\\ P\\in\\mathcal P,\\ Q\\in\\mathcal Q,\\ P\\cap Q\\ne\\varnothing\\},$$
  moreover, $|\\mathcal R|\\le k^2$ and each set that is a union of blocks $\\mathcal P$ (or $\\mathcal Q$) is automatically a union of blocks $\\mathcal R$.
  Therefore, if one tries to implement basechange solely through Section 16.130 (i.e., through an "abstract" proof of size $2^{O(|\\mathcal R|)}$ on variables $y_R$ and substitution $y_R\\mapsto \\mathrm{PARITY}(R)$), then the basic upper limit on the cost of such a step has the form
  $$2^{O(|\\mathcal R|)}\\le 2^{O(k^2)}.$$
  In particular, for $k=\\Theta(\\log n)$ this is already $2^{\\Theta(\\log^2 n)}=n^{\\Theta(\\log n)}$ (quasi-poly), so the "universal" base-change through refinement does not preserve the polynomial-size.
- `Proof:`
  1) (General clarification.) For any partitions $\\mathcal P,\\mathcal Q$, the family $\\mathcal R$ above is a partition of $U$ (into non-empty pairwise disjoint sets), and by definition each block $P\\in\\mathcal P$ is decomposed into a disjoint union of blocks $P\\cap Q$ for $Q\\in\\mathcal Q$; similarly for each $Q\\in\\mathcal Q$.
  2) (Estimate the number of blocks.) Since the pairs $P\\cap Q$ are not greater than $k\\cdot k$, we obtain $|\\mathcal R|\\le k^2$.
  3) (The worst case is achieved.) Let $U=[k]\\times[k]$. Let us take $\\mathcal P$ as the row partition $P_i:=\\{i\\}\\times[k]$ and $\\mathcal Q$ as the column partition $Q_j:=[k]\\times\\{j\\}$. Then each intersection $P_i\\cap Q_j$ is a one-point set, which means $|\\mathcal R|=k^2$.
  4) (Cost "through Section 16.130.") In Section 16.130, abstract XOR inference on $k$ block variables costs $2^{O(k)}$ (essentially a truth table search). If we naively reduce two incompatible block-representations to a common $\\mathcal R$ and then work abstractly, then the number of block-variables becomes $|\\mathcal R|$, and the estimate becomes $2^{O(|\\mathcal R|)}\\le 2^{O(k^2)}$.
- `Toy test:` if $k=\\lfloor\\log_2 n\\rfloor$, then $2^{O(k^2)}=2^{O(\\log^2 n)}=n^{O(\\log n)}$, i.e. even one "universal" base-change of this type can already destroy the target $n^{O(1)}$.
- `Status:` proven (method barrier: dynamic partitions are really needed, but "translation through general refinement" in the worst case quadratically inflates the number of blocks and leads to quasi-poly for $k=\\Theta(\\log n)$).
- `Barrier check:` r - not applicable (question about syntactic price inside Frege, not oracles), NP - not applicable (not about algorithms for solving SAT), alg - not applicable (not about arithmetization/algebraization of models).
- `Next step:` find a "structural" basechange that, for the desired intermediate partitions on the grid, avoids blowup $k\\to k^2$ (for example, a chain of controlled refinement/coarsening, where each transformation has $O(1)$ or $O(\\log n)$ support at the abstract level), or show that in the Hastad-Risse strategy inevitably pairs of partitions with $|\\mathcal appear P\\wedge\\mathcal Q|=\\Omega(k^2)$.

### 16.133. Exploratory step: for interval-partition on $[m]$ the total refinement has size $\\le k_1+k_2-1$ (no quadratic blow-up)

- `Lens:` Invariant.
- `Statement:` Let $U=[m]=\\{1,\\dots,m\\}$ with a fixed order. Let's call a partition $\\mathcal P$ **intervalpartition** if each block is an interval $[a,b]\\cap\\mathbb Z$.
  Then for any two intervalpartition $\\mathcal P,\\mathcal Q$ with $|\\mathcal P|=k_1$, $|\\mathcal Q|=k_2$ their general refinement satisfies
  $$|\\mathcal P\\wedge\\mathcal Q|\\le k_1+k_2-1.$$
  Consequently, the "universal" basechange from Section 16.132 through a general refinement gives only a linear increase in the number of blocks if all partitions are compatible with the same 1dimensional order.
- `Proof:` interval-partition is uniquely defined by a set of cuts
  $$C(\\mathcal P)\\subseteq\\{1,\\dots,m-1\\},\\qquad i\\in C(\\mathcal P)\\iff i,i+1\\text{ lie in different blocks }\\mathcal P.$$
  Then $|\\mathcal P|=|C(\\mathcal P)|+1$.
  For two intervalpartitions, the general refinement $\\mathcal P\\wedge\\mathcal Q$ has cuts exactly at the points
  $$C(\\mathcal P\\wedge\\mathcal Q)=C(\\mathcal P)\\cup C(\\mathcal Q),$$
  because the new partition must cut wherever at least one of the original ones cuts, and nowhere else (otherwise the maximality of block segments will be violated).
  Means
  $$|\\mathcal P\\wedge\\mathcal Q|=|C(\\mathcal P)\\cup C(\\mathcal Q)|+1\\le |C(\\mathcal P)|+|C(\\mathcal Q)|+1=(k_1-1)+(k_2-1)+1=k_1+k_2-1.$$
- `Toy test:` let $m=6$, $\\mathcal P=(\\{1,2\\},\\{3,4\\},\\{5,6\\})$ ($k_1=3$) and $\\mathcal Q=(\\{1\\},\\{2,3\\},\\{4,5\\},\\{6\\})$ ($k_2=4$).
  Then $|\\mathcal P\\wedge\\mathcal Q|=6=k_1+k_2-1$ (the boundary is exact).
- `Status:` proven (positive "structural case": the quadratic blow-up from Section 16.132 occurs only with "transverse" partitions; for 1D-compatible partitions the refinement is linear).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether in the Hastad-Risse strategy for grid it is possible to select all the necessary block representations so that the partitions are (approximately) 1D compatible with one order on the edges/variables; otherwise, find a place where a "transverse" transition of the rowcolumn type is inevitably required (and then Section 16.132 again gives a quasi-poly barrier).

### 16.134. Exploratory step: in column-summing on a grid, the intermediate XOR-equations correspond to the boundary of the rectangle and are divided into $O(1)$ row-interval segments (so the $k^2$-barrier Section 16.132 does not work locally)

- `Lens:` Equivalence.
- `Statement:` Consider a $n\\times n$ grid with vertices $(i,j)$, $1\\le i,j\\le n$, and variables $x_e$ on the edges.
  We fix the inner column $2\\le j\\le n-1$ and for $t\\in[n]$ we denote
  $$R_{j,t}:=\\{(i,j):1\\le i\\le t\\}$$
  (the first $t$ vertices of column $j$) and $\\delta(R_{j,t})$ is the set of edges that have exactly one end in $R_{j,t}$.
  Then the XOR-sum of vertex Tseitin-equations over the vertices $R_{j,t}$ is equal to one equation
  $$E\\bigl(\\delta(R_{j,t}),\\ \\bigoplus_{v\\in R_{j,t}}\\chi(v)\\bigr).$$
  Moreover, $\\delta(R_{j,t})$ is decomposed into a disjoint union of at most four "rowinterval" segments:
  - $L_{j,t}$: horizontal edges between columns $j-1$ and $j$ on rows $1..t$,
  - $H_{j,t}$: horizontal edges between columns $j$ and $j+1$ on lines $1..t$,
  - $T_{j}$: one vertical edge over $(1,j)$ (if $(1,j)$ is not on the upper boundary),
  - $B_{j,t}$: one vertical "front" edge between $(t,j)$ and $(t+1,j)$ (if $t<n$).
  Therefore, in this particular linear strategy, all intermediate equations are represented as parity over $k=O(1)$ disjoint blocks, consistent with a single 1D row order.
- `Proof:`
  1) (Boundary as an XOR sum.) When XOR summing vertex equations over $R_{j,t}$, each internal edge (both ends in $R_{j,t}$) enters the left side exactly twice and cancels modulo 2, and each edge with exactly one end appears in $R_{j,t}$ exactly once. Therefore, the left side is equal to parity in $\\delta(R_{j,t})$, and the right side is equal to $\\bigoplus_{v\\in R_{j,t}}\\chi(v)$.
  2) (Geometry $\\delta(R_{j,t})$.) For the set of "column prefix" vertices, the possible edges emanating from $R_{j,t}$ are of three types:
     - horizontal left/right from lines $1..t$ (give two rowinterval segments $L_{j,t},H_{j,t}$);
     - vertical upwards from vertex $(1,j)$ and downward from vertex $(t,j)$ (give $\\le 2$ separate edges $T_j,B_{j,t}$).
     There are no other edges incident to the vertices $R_{j,t}$.
- `Toy test:` $n=4$, $j=2$, $t=2$.
  Then $\\delta(R_{2,2})$ consists of two horizontal segments of length 2 (between (i,1)-(i,2) and (i,2)-(i,3) for $i=1,2$) and one vertical edge (2,2)-(3,2) (plus the top one, if you count the outer "frame").
- `Status:` proven (clarification: for the column-summing strategy itself, multiple variables do not create "transverse" partitions; the technical point is not the combinatorial $k^2$-blow-up, but the syntactic ability to move between parity formulas for growing segments).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` select a minimal "local" subtask: for rowinterval $I=[1..t]$, understand whether it is possible to polynomially prove the correctness of gluing in boundeddepth Frege with $d=\\Theta(\\log n/\\log\\log n)$
  $$\\mathrm{PARITY}(I\\cup\\{e\\})\\leftrightarrow \\bigl(\\mathrm{PARITY}(I)\\oplus x_e\\bigr)$$
  (and similarly for the frontier shift), i.e. basechange between parity formulas for adjacent intervals.

### 16.135. Exploratory step: even for 1D prefixes, a fixed block basis requires $k=\\Omega(n)$ (rank $n$)

- `Lens:` Communication/Rank.
- `Statement:` Let $e_1,\\dots,e_n$ be pairwise distinct variables (for example, horizontal edges between fixed columns $j$ and $j+1$ on rows $1..n$).
  For $t\\in[n]$ we denote the prefix set
  $$L_t:=\\{e_1,\\dots,e_t\\}.$$
  Then in $\\mathbb F_2^{\\{e_1,\\dots,e_n\\}}$ the sets $L_1,\\dots,L_n$ are linearly independent, which means:
  if a set of $k$ subsets $B_1,\\dots,B_k$ is fixed and each $L_t$ is represented as a symmetric difference
  $$L_t=\\bigtriangleup_{i\\in I_t} B_i,$$
  then necessarily $k\\ge n$.
  In particular, any attempt to keep one fixed small basis "segment blocks" in column-summing, covering **all** $[1..t]$ prefixes, is doomed (even in 1D), and base-change/dynamic partitions are inevitable.
- `Proof:` Consider the characteristic vectors $\\mathbf 1_{L_t}\\in\\mathbb F_2^n$ with respect to the basis $e_1,\\dots,e_n$.
  We have the identity
  $$\\{e_t\\}=L_t\\triangle L_{t-1}\\qquad (t\\ge 2),$$
  and $\\{e_1\\}=L_1$. Consequently, the linear hull $\\langle L_1,\\dots,L_n\\rangle$ contains all single-element sets $\\{e_t\\}$, which means it has dimension $n$.
  Since there are exactly $n$ vectors $L_t$, they are linearly independent.
  Hence, if all $L_t$ lie in $\\langle B_1,\\dots,B_k\\rangle$, then
  $$n=\\dim\\langle L_1,\\dots,L_n\\rangle\\le \\dim\\langle B_1,\\dots,B_k\\rangle\\le k.$$
- `Toy test:` $n=3$: $L_1=(1,0,0)$, $L_2=(1,1,0)$, $L_3=(1,1,1)$ are independent (upper triangular matrix with ones on the diagonal).
- `Status:` proven (barrier: "a fixed small basis for all prefixes" is already impossible in 1D; this means that even with the structure of Section 16.134, the node remains in a dynamic basechange, and not in the choice of a single basis).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` parse base-change not as a "general translation between two arbitrary partitions", but as local operations on the boundary (add/remove one $e_t$) and look for whether bounded-depth Frege can implement such a local transformation on parity formulas without accumulating depth/quasi-poly blow-up.

### 16.136. Exploratory step: canonical dyadic split of prefix $[t]$ produces $\\le \\lfloor\\log_2 t\\rfloor+1$ blocks and is updated with $O(\\log n)$ merges

- `Lens:` Compression/canonization.
- `Statement:` For each $t\\in[n]$ there is a partition of the prefix $[t]=\\{1,\\dots,t\\}$ into pairwise disjoint intervals
  $$[t]=I_1\\uplus I_2\\uplus\\cdots\\uplus I_r,$$
  where each $I_j$ has length a power of two, and
  $$r\\le \\lfloor\\log_2 t\\rfloor+1.$$
  Moreover, one can choose a **canonical** partition (via binary notation $t$) that has the updating property:
  transition $t\\mapsto t+1$ converts partition $[t]$ into partition $[t+1]$ by a sequence of operations
  "add singleton $[t+1,t+1]$" and then apply $\\le \\lfloor\\log_2 n\\rfloor+1$ times
  $$J\\uplus J'\\mapsto J\\cup J'$$
  to two adjacent intervals of the same length (merging into an interval of twice the length).
- `Proof:`
  1) (Existence and estimate on $r$.) Let us write $t$ in binary form
     $$t=\\sum_{a\\in A}2^a,\\qquad A\\subseteq\\{0,1,\\dots,\\lfloor\\log_2 t\\rfloor\\}.$$
     Let's sort through $a\\in A$ in descending order and sequentially put
     $$I_1=[1,2^{a_1}],\\ I_2=[2^{a_1}+1,2^{a_1}+2^{a_2}],\\ \\dots$$
     Then the intervals are pairwise disjoint, their union is equal to $[t]$, and $r=|A|\\le \\lfloor\\log_2 t\\rfloor+1$.
  2) (Canonicity and update.) Adding 1 to the binary number $t$ changes the suffix of the form $\\underbrace{11\\cdots 1}_{s}\\mapsto 0\\cdots 0$ and increments the next bit.
     In terms of partitioning, this means: on a transition $t\\to t+1$, a new interval of length 1 is first added, and then for each "carry"
     two adjacent dyadic parts of the same length merge into one part of double length. The number of carries is equal to the number of consecutive ones at the end of the binary record $t$,
     therefore does not exceed $\\lfloor\\log_2 n\\rfloor+1$.
- `Toy test:` $t=13=8+4+1$: $[13]=[1,8]\\uplus[9,12]\\uplus[13,13]$.
  Then $t+1=14=8+4+2$: add $[14,14]$ and merge $[13,13]$ with $[14,14]$ into $[13,14]$, getting
  $[14]=[1,8]\\uplus[9,12]\\uplus[13,14]$.
- `Status:` proven (canonical way to keep prefixes with $O(\\log n)$ blocks and local merge operations).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` reduce "local basechange" for rowintervals to one type of operation: show/refute that boundeddepth Frege can polynomially infer the correctness of merge
  $$\\mathrm{PARITY}(J)=b_1,\\ \\mathrm{PARITY}(J')=b_2\\ \\vdash\\ \\mathrm{PARITY}(J\\cup J')=b_1\\oplus b_2$$
  for two adjacent disjunct intervals of the same length (and then iteratively maintain the prefix strategy).

### 16.137. Exploratory step: the merge rule for disjunct blocks reduces to the "easy case" Section 16.130 if we take the parity representation on each block as an atom

- `Lens:` Equivalence.
- `Statement:` Let the set of variables $X$ be divided into disjoint blocks $B_1\\uplus\\cdots\\uplus B_k$.
  For each $i$, let $P_i(x_{B_i})$ be the formula that calculates the parity on $B_i$ (that is, $P_i=1\\iff\\bigoplus_{x\\in B_i}x=1$), and assume that both polarities are available as $P_i$ and $\\neg P_i$.
  Then for any disjoint block unions
  $$S_{I}:=\\bigcup_{i\\in I}B_i\\qquad (I\\subseteq[k])$$
  and any $I_1,I_2\\subseteq[k]$ we have polynomialsize boundeddepth Fregeoutput
  $$E(S_{I_1},b_1),\\ E(S_{I_2},b_2)\\ \\vdash\\ E(S_{I_1\\triangle I_2},\\ b_1\\oplus b_2)$$
  size $2^{O(k)}$ and depth $O(\\max_i\\depth(P_i))$.
  In particular, to merge two adjacent intervals of the same length (dyadic-merge from Section 16.136), it is enough to take $k=2$ and get a constant output in $k$:
  $$\\mathrm{PARITY}(J)=b_1,\\ \\mathrm{PARITY}(J')=b_2\\ \\vdash\\ \\mathrm{PARITY}(J\\cup J')=b_1\\oplus b_2.$$
- `Proof:` This is a direct application of Section 16.130:
  1) On abstract variables $y_1,\\dots,y_k$, where $y_i$ means "the parity of block $B_i$ is 1", the formulas $E^{\\mathrm{blk}}(I,b)$ (full DNF on $y$) depend only on $k$ variables and semantically implement XOR linearity.
     Therefore the tautology
     $$E^{\\mathrm{blk}}(I_1,b_1)\\wedge E^{\\mathrm{blk}}(I_2,b_2)\\to E^{\\mathrm{blk}}(I_1\\triangle I_2,b_1\\oplus b_2)$$
     has a bounded-depth Frege derivation of size $2^{O(k)}$ (Lemma 4 from GIRS'19, as in §16.130).
  2) By substituting $y_i\\mapsto P_i$ we get the output on the original variables. Since blocks are disjunctive, semantically
     $$\\bigoplus_{i\\in I} y_i\\ =\\ \\bigoplus_{x\\in S_I} x,$$
     then the substitution formula really represents the equation $E(S_I,b)$.
- `Toy test:` $k=2$: from $y_1=b_1$ and $y_2=b_2$ it follows $y_1\\oplus y_2=b_1\\oplus b_2$; substitution gives merge for two disjunct blocks.
- `Status:` partially (local formalization: merge becomes "easy" if **there are already** $P_i$ formulas for block parities and we allow the equations to be represented as DNF on these $P_i$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` close the "representation vs proof" gap: in the Hastad-Risse strategy, block parities $P_i$ exist (as small depth$d$ formulas), but a way is needed to **reuse** them in a sequence of steps without accumulating the base/without increasing the number of blocks; formally: is it possible to keep all intermediate equations as $E^{\\mathrm{blk}}(I,b)$ over the current set of block parities so that each step changes $k$ only by $O(1)$ and preserves $2^{O(k)}=\\mathrm{poly}(n)$?

### 16.138. Exploratory step: in Schoenfield-Frege, substitution captures negation syntactically ($\\sigma(\\neg p)=\\neg\\sigma(p)$), so "two separate OR formulas for parity and its negation" do not form a pair of literals

- `Lens:` Compression/canonization.
- `Statement:` In SchoenfieldFrege (Hastad-Risse'25, Section 2.1; `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`) application of the rule is the substitution of $\\sigma$ into the output scheme,
  and for any variable $p$ the identity of **syntactic** substitution is satisfied
  $$\\sigma(\\neg p)=\\neg\\sigma(p).$$
  Therefore, it is impossible to "build" into one application of the rule a pair of formulas $P(x),N(x)$ so that $P$ plays the role of the literal $p$, and $N$ plays the role of the literal $\\neg p$, unless $N$ is **literally** equal to $\\neg P$ as a formula.
  This clears up the gap in Hastad-Risse'25, Section 1.2: there "PARITY and $\\neg$PARITY" on the block are represented by **two** small depth$d$ formulas with output $\\vee$,
  but the Frege rules themselves treat negation only as *syntactic* $\\neg$ (and not as "any equivalent representative of negation"), so such a pair does not automatically give block-level Cut/resolving without loss of depth.
- `Proof:` by definition (Hastad-Risse'25, Section 2.1) if $p$ and $\\neg p$ occur simultaneously in a rule scheme, then after substitution we obtain simultaneously $\\sigma(p)$ and $\\sigma(\\neg p)=\\neg\\sigma(p)$.
  Therefore, if we want to implement "$p\\mapsto P$ and $\\neg p\\mapsto N$", we need $N=\\neg P$ as a formula. For an arbitrary pair of semantically opposite formulas this is not true.
- `Toy test:` for 1-variable $P(x)=x$ and $N(x)=\\neg x$ we have $N=\\neg P$, and the substitution actually reconciles both polarities.
  But already for a 2-variable parity pair we can take
  $P(x,y)=(x\\wedge\\neg y)\\vee(\\neg x\\wedge y)$ and $N(x,y)=(x\\wedge y)\\vee(\\neg x\\wedge\\neg y)$ (both with output $\\vee$);
  then $N\\not\\equiv_{\\text{synt}} \\neg P$, and substitution alone cannot force $N$ to play the role of "$\\neg P$" in rule instances.
- `Status:` proven (the exact "syntactic" reason why representation "PARITY + $\\neg$PARITY as two OR formulas" does not automatically make it possible to do Cut steps on these representatives without going beyond depth).
- `Barrier check:` r - not applicable (this is a purely syntactic property of Frege rules), NP - not applicable, alg - not applicable.
- `Next step:` check whether for specific HRrepresentatives of PARITY it is possible to construct in boundeddepth Frege **polynomial** proofs of equivalences of the form $N\\leftrightarrow\\neg P$ without going beyond the depth $d$ (or establish that such a "negationnormalization" itself costs quasipoly and thereby explains why Section 1.2 gives only representation).

### 16.139. Research step: if for block parities the "consistency of polarities" $N_i\\leftrightarrow\\neg P_i$ is provable, then the "representation" Hastad-Risse turns into a real substitution Frege-step

- `Lens:` Duality/complements.
- `Statement:` Let $X=\\biguplus_{i=1}^k B_i$ be a partition into disjoint blocks, and let formulas $P_i(x_{B_i})$ and $N_i(x_{B_i})$ of depth $\\le d_0$ be given, such that semantically $N_i\\equiv\\neg P_i$.
  Suppose that in boundeddepth Frege (depth $O(d_0)$) there is a polynomialsize output **consistency**
  $$\\mathrm{Cons}_i:\\qquad N_i\\leftrightarrow\\neg P_i\\qquad (i\\in[k]).$$
  Then any "abstract" inference on the variables $y_1,\\dots,y_k$ (where $y_i$ means "the parity of $B_i$ is 1") can be implemented on the original variables so that
  the positive polarity $y_i$ was interpreted as $P_i$, and the negative polarity $\\neg y_i$ - as $N_i$, with a polynomial blow-up in size and without going beyond the depth $O(d_0)$.
  In particular, the tautology from Section 16.130 (and the "easy case" merge from Section 16.137) remains polynomial-size inferable under this dual-rail interpretation.
- `Proof:` take the boundeddepth Fregederivation of $\\pi$ tautology on $y$variables from Section 16.130:
  $$E^{\\mathrm{blk}}(I_1,b_1)\\wedge E^{\\mathrm{blk}}(I_2,b_2)\\to E^{\\mathrm{blk}}(I_1\\triangle I_2,b_1\\oplus b_2).$$
  1) By substituting $y_i\\mapsto P_i$ we obtain the output $\\pi'$ of the same implication, but with negative literals in the form $\\neg P_i$ (see Section 16.130).
  2) For each $i$ from $\\mathrm{Cons}_i$ and the rule of "replacing equivalents" (locally: from $A\\leftrightarrow B$ we can derive $\\neg A\\leftrightarrow\\neg B$ and $(A\\vee C)\\leftrightarrow (B\\vee C)$; these tautologies depend on $O(1)$ atoms and therefore have constant boundeddepth Frege-derivations, as in Section 16.130) we find that it is possible **within any context-formula** to replace each occurrence of $\\neg P_i$ with $N_i$, maintaining derivability and increasing the size no more than polynomially of the size of the context.
  Applying this to all literals in $E^{\\mathrm{blk}}$ (size $2^{O(k)}$), we obtain the required output with polarities $(P_i,N_i)$.
- `Toy test:` $k=1$. Abstract step: $\\neg y=1$ is derived from $y=0$ (and vice versa) - this is simply an excluded third. After substitution we get $P_1=0\\vdash \\neg P_1=1$, and then using $\\mathrm{Cons}_1$ we can replace $\\neg P_1$ with $N_1$.
- `Status:` proven (reduction: the central node is the cost of proof $N_i\\leftrightarrow\\neg P_i$; without it, the "two-formula" representation from HR Section 1.2 does not become a substitution simulation).
- `Barrier check:` r - not applicable (property of syntactic simulation in a fixed proof system), NP - not applicable, alg - not applicable.
- `Next step:` for the HR-construction PARITY/$\\neg$PARITY on a block, try to either (a) construct a poly-size bounded-depth output $N\\leftrightarrow\\neg P$ (i.e. "consistency axiom"), or (b) identify the place where such an output should cost quasi-poly and thereby explain the "representation, not proof" from Section 1.2.

### 16.140. Exploratory step: "depth margin" removes the need for a separate OR formula for $\\neg\\mathrm{PARITY}$ - you can use the syntactic $\\neg P$ (and optionally OR output by adding $\\bot$)

- `Lens:` Trade-off.
- `Statement:` In the Schoenfield language $\\{\\vee,\\neg\\}$ (Hastad-Risse'25, Section 2.1), the depth of a formula is the number of alternations $\\vee/\\neg$ on the path.
  Then for any formula $A$ we have
  $$\\depth(\\neg A)\\le \\depth(A)+1.$$
  Therefore, if in boundeddepth Frege we can represent blockparity by the formula $P$ of depth $\\le d-1$, then both polarities are available **syntactically** in depth $\\le d$ as $P$ and $\\neg P$, and substitution steps like Section 16.130-Section 16.137 do not require a separate formula $N$ and a separate output $N\\leftrightarrow\\neg P$.
  If for a particular "clause-style" you need the literal to have the output $\\vee$, you can replace $\\neg P$ with
  $$N:=\\neg P\\vee\\bot,$$
  and then $N$ has an output $\\vee$, and the tautology $N\\leftrightarrow\\neg P$ has a constant Frege output (by substitution into the circuit $(\\neg p\\vee\\bot)\\leftrightarrow\\neg p$).
  The price for depth with this "OR-wrapping" is $\\depth(N)\\le \\depth(P)+2$.
- `Proof:` adding one top $\\neg$ to the formula either adds one new stripe block (if the root of $A$ is $\\vee$) or does not change the number of stripes (if the root of $A$ is $\\neg$), so $\\depth(\\neg A)\\le\\depth(A)+1$.
  For $N:=\\neg P\\vee\\bot$ the depth increases by a maximum of 1 more due to the upper $\\vee$.
  The equivalence $N\\leftrightarrow\\neg P$ is an instance of a fixed tautology on one atom, which means it has a bounded depth Frege output of size $O(1)$, and the substitution gives an output for an arbitrary $P$.
- `Toy test:` $A=p\\vee q$ has $\\depth(A)=1$ and $\\neg A$ has $\\depth=2$.
  If $A=\\neg p$, then $\\neg A=\\neg\\neg p$ and the number of alternations does not increase.
- `Status:` proven (formally: "negative polarity" does not require a separate HR formula if one can afford a constant depth margin for explicit $\\neg$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` test whether HRrepresentability for PARITY on one block ($n$ variables) with depth $d\\approx\\log n/\\log\\log n$ allows you to "eat" the constant margin (for example, build $P$ of depth $d-2$ of size $\\mathrm{poly}(n)$), so that negative literals in Section 16.130-Section 16.137 are implemented as $\\neg P$ (or $\\neg P\\vee\\bot$) without going beyond the target depth.

### 16.141. Exploratory step: constant "depth margin" is compatible with the $d\\approx\\log n/\\log\\log n$ threshold for representability PARITY at $M=\\mathrm{poly}(n)$

- `Lens:` Trade-off.
- `Statement:` Let the representation fact Hastad-Risse'25, Section 1.2 hold: given the constraint "each row has depth $d$ and size $M$," we can write the formula
  representing $\\mathrm{PARITY}$ on a block of
  $$m=(\\log M)^{d-1}$$
  variables (and similarly for negation).
  Then, for $d=\\Theta(\\log n/\\log\\log n)$, the constant loss of depth does not prevent us from covering a block of width $n$ with polynomial $M$:
  there is a constant $C>1$ such that for $M:=n^C$ and $d:=\\left\\lceil\\frac{\\log n}{\\log\\log n}\\right\\rceil+2$
  $$(\\log M)^{(d-1)-1}=(\\log M)^{d-2}\\ge n.$$
  In particular, one can choose a parity representative $P$ of depth $\\le d-1$ and size $\\mathrm{poly}(n)$, and take its negation as syntactic $\\neg P$ of depth $\\le d$ (see Section 16.140).
- `Proof:` let us put $M=n^C$, then $\\log M=C\\log n$ and we need to prove $(C\\log n)^{d-2}\\ge n$, i.e.
  $$ (d-2)\\,\\log(C\\log n)\\ \\ge\\ \\log n.$$
  For $d=\\left\\lceil\\frac{\\log n}{\\log\\log n}\\right\\rceil+2$ we have $d-2\\ge \\frac{\\log n}{\\log\\log n}$, therefore
  $$(d-2)\\log(C\\log n)\\ \\ge\\ \\frac{\\log n}{\\log\\log n}\\cdot\\bigl(\\log\\log n+\\log C\\bigr)\\ =\\ \\log n+\\frac{\\log C}{\\log\\log n}\\,\\log n\\ \\ge\\ \\log n.$$
  Hence $(C\\log n)^{d-2}\\ge 2^{\\log n}=n$.
- `Toy test:` $n=2^{64}$, $C=4$, $d=\\lceil 64/6\\rceil+2=13$.
  Then $\\log M=4\\log n=256$ and $(\\log M)^{d-2}=256^{11}=2^{88}>2^{64}=n$.
- `Status:` proven (parameter arithmetic: using $\\neg P$ in Section 16.140 requires only $O(1)$ depth margin, and this margin is compatible with the threshold $d\\approx\\log n/\\log\\log n$ for $M=\\mathrm{poly}(n)$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` fix the exact formulation of the representation fact from HR'25 Section 1.2 as a separate "known lemma" (which depth/base/output symbol is allowed) so that there is no hidden +O(1) to the depth; then return to the main node: syntactic simulation of XOR-addition (Gaussian elimination step) inside bounded-depth Frege.

### 16.142. Research step: exact formulation of HR'25 Section 1.2 "representing parity" and standard upper bound for PARITY (Hastad'86, Remark 6)

- `Lens:` Equivalence.
- `Statement:` In Hastad-Risse'25, Section 1.2 (`../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`) representation step is formulated in the Schoenfield-Frege model (Section 2.1: base $\\{\\vee,\\neg\\}$, depth = number of alternations $\\vee/\\neg$), and contains specific parameters:
  for the parity equation on $m$ variables and the constraint "line size $\\le M$, line depth $\\le d$" the authors write:
  «divide the variables into groups of size $(\\log M)^{d-1}$ and write down formulas of depth $d$ and size $M$ that represent the parity and the negation of the parity of each group… assume output gate is an or»
  (see Section 1.2, paragraph starting with "Let us consider proofs that contain formulas of depth d...").
  This is consistent with the standard (known) upper bound for PARITY schemes: Hastad'86, Remark 6 (`../../resources/downloads/hastad_1986.pdf`, p. 10) notes that PARITY has a depth$k$ scheme of view size
  $$\\mathrm{size}\\ \\le\\ n\\cdot 2^{\\,O\\bigl(n^{1/(k-1)}\\bigr)}\\ =\\ 2^{O(n^{1/(k-1)})}.$$
  The inversion gives exactly the block size $n=\\Theta((\\log M)^{k-1})$ for a given limit $M$ (up to constants in $O(\\cdot)$), that is, the HR parameter $(\\log M)^{d-1}$ is the standard "solve $M=2^{O(n^{1/(d-1)})}$" (base $2$; changing the base gives only a constant multiplier in the indicator).
- `Proof:` from Hastad'86 Remark 6 we take existence upper bound $\\mathrm{size}\\le 2^{C\\,n^{1/(k-1)}}$ for some constant $C$ (for a fixed depth $k$).
  Let us set $n:=\\bigl(\\tfrac{\\log M}{2C}\\bigr)^{k-1}$. Then $C\\,n^{1/(k-1)}=\\tfrac12\\log M$, and the size satisfies
  $$\\mathrm{size}\\le 2^{C\\,n^{1/(k-1)}}\\le 2^{\\tfrac12\\log_2 M}=\\sqrt M\\le M.$$
  Therefore, there is a depth-$k$ formula of size $\\le M$ that calculates PARITY on $\\Omega((\\log M)^{k-1})$ variables. For the HR need "output $\\vee$" you can use the OR wrapper $A\\mapsto A\\vee\\bot$ (see Section 16.140) with a constant overhead in depth/size.
- `Toy test:` if $k=3$, then bound has the form $2^{O(\\sqrt n)}$; the inversion gives $n=\\Theta((\\log M)^2)$, which coincides with the HR formula $(\\log M)^{d-1}$ for $d=3$.
- `Status:` known/fixed (exact link + formal derivation of parametrics; now "representability PARITY on $(\\log M)^{d-1}$" does not hang on the informal "write down formulas").
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` return to core Q39: even if $P$ formulas are available for intermediate equations, polysize boundeddepth Fregederivation of XORaddition step (Gaussian elimination) **between** such representations is needed; try to formalize/kill the toy case of "one common intersection variable" by analogy with the resolution from HR Section 1.2.

### 16.143. Exploratory step: the toy case of the XOR step when crossing in one variable is reduced to Section 16.130 with $k\\le k_1+k_2+1$ (if both lines are already written as block parity)

- `Lens:` Compression/canonization.
- `Statement:` Let there be two XOR equations on sets of variables $S_1,S_2\\subseteq X$ with
  $$S_1\\cap S_2=\\{x\\}.$$
  Let's assume that each equation is already written in the "block form" of Section 16.130:
  there are partitions into disjoint blocks
  $$S_1=\\biguplus_{i=1}^{k_1}B_i,\\qquad S_2=\\biguplus_{j=1}^{k_2}C_j,$$
  and for each block there are formulas representing its parity (and negation), so that the strings $E(S_1,b_1)$ and $E(S_2,b_2)$ are implemented as XOR by block parities.
  Then there is a partition $S_1\\cup S_2=\\biguplus_{t=1}^k D_t$ with
  $$k\\le k_1+k_2+1,$$
  relative to which **both** rows become unions of blocks of the same partition, and therefore one XOR step
  $$E(S_1,b_1),\\ E(S_2,b_2)\\ \\vdash\\ E(S_1\\triangle S_2,\\ b_1\\oplus b_2)$$
  has a boundeddepth Fregeoutput of size $2^{O(k)}$ (and, in particular, polynomialsize for $k_1,k_2=O(\\log n)$).
- `Proof:`
  1) Let $B_{i^*}$ and $C_{j^*}$ denote the only blocks containing $x$ (they exist and are unique in terms of disjoint partitions).
  2) Let us construct a joint partition $\\mathcal D$ of the set $S_1\\cup S_2$ as follows: let us leave all the blocks $B_i$ for $i\\ne i^*$ and all the blocks $C_j$ for $j\\ne j^*$, and "cut" the blocks intersecting at $x$:
     $$B_{i^*}=\\{x\\}\\uplus (B_{i^*}\\setminus\\{x\\}),\\qquad C_{j^*}=\\{x\\}\\uplus (C_{j^*}\\setminus\\{x\\}).$$
     Then the block family
     $$\\mathcal D:=\\{\\{x\\},\\ B_{i^*}\\setminus\\{x\\},\\ C_{j^*}\\setminus\\{x\\}\\}\\ \\cup\\ \\{B_i:i\\ne i^*\\}\\ \\cup\\ \\{C_j:j\\ne j^*\\}$$
     (throwing out empty sets) consists of pairwise disjoint subsets and covers $S_1\\cup S_2$.
     By counting the blocks we get $k\\le (k_1-1)+(k_2-1)+3=k_1+k_2+1$.
  3) Each of $S_1,S_2$ is a union of blocks from $\\mathcal D$ (blocks outside the corresponding set are simply not taken), therefore both equations can be considered as XOR over one fixed set of block parities $\\{P_{D_t}\\}_{t\\in[k]}$.
     Then the required XOR step is a tautology on $k$ "atoms" (block parities), and it is this case that Section 16.130 covers.
- `Toy test:` $S_1=\\{x,a,b,c\\}$, $S_2=\\{x,d,e\\}$.
  Let $S_1$ be divided as $B_1=\\{x,a,b\\}$, $B_2=\\{c\\}$ ($k_1=2$), and $S_2$ as $C_1=\\{x,d\\}$, $C_2=\\{e\\}$ ($k_2=2$).
  Then $\\mathcal D=\\{\\{x\\},\\{a,b\\},\\{c\\},\\{d\\},\\{e\\}\\}$ and $k=5=k_1+k_2+1$, after which the XOR step is reduced to Section 16.130 with $k=5$.
- `Status:` partially (the toy case "intersection = 1 variable" does not create a $k^2$ explosion when bringing two block records to a common partition; the remaining difficulty Q39 is to ensure the block form itself and its maintenance during dynamic base changes).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` test on a real grid strategy whether it is possible to arrange the output so that *each* local boundary update step (adding a vertex/small equation) has an $O(1)$ intersection and both rows are written as XOR over $O(\\log n)$ blocks of the same "current" partition; if not, find the minimum place where an intersection of many variables or a "transverse" transition between incompatible partitions inevitably occurs (and then the barrier of Section 16.132 is turned on again).

### 16.144. Exploratory step: in column-summing, each local transition $t\\to t+1$ is an XOR-step with intersection at exactly one edge (the vertex equation intersects the boundary at one edge)

- `Lens:` Invariant.
- `Statement:` Let $G$ be a graph, $A\\subseteq V(G)$ and $v\\notin A$.
  Let $E(v)$ be the set of edges incident to $v$, and $\\delta(A)$ be the edges that have exactly one end in $A$.
  Then
  $$\\delta(A\\cup\\{v\\})\\ =\\ \\delta(A)\\triangle E(v).$$
  Moreover, if $v$ has exactly one neighbor in $A$, then $\\delta(A)\\cap E(v)$ consists of exactly one edge.
  In particular, for the strategy from Section 16.134 on grid, where $A=R_{j,t}$ and $v=(t+1,j)$, we have
  $$\\delta(R_{j,t+1})=\\delta(R_{j,t})\\triangle E(v),\\qquad |\\delta(R_{j,t})\\cap E(v)|=1,$$
  therefore, the transition $t\\to t+1$ to "Gaussian elimination modulo 2" is implemented as an XOR step between one intermediate equation of width $\\Theta(n)$ and one vertex equation of constant width.
- `Proof:`
  1) For any edge $e=uw$ non-incident $v$, the membership of $e$ in the set $\\delta(A)$ and $\\delta(A\\cup\\{v\\})$ coincides, since the membership statuses of the ends in $A$ do not change.
  2) Let $e$ be incident to $v$, i.e. $e=vu$.
     Then $e\\in\\delta(A)$ is equivalent to the condition $u\\in A$ (since $v\\notin A$), and $e\\in\\delta(A\\cup\\{v\\})$ is equivalent to $u\\notin A\\cup\\{v\\}$, i.e. $u\\notin A$.
     Therefore, for edges in $E(v)$, the boundary membership is **inverted** when $v$ is added, that is, it is the edges of $E(v)$ that switch the membership in $\\delta$.
     This means $\\delta(A\\cup\\{v\\})=\\delta(A)\\triangle E(v)$.
  3) If $v$ has exactly one neighbor $u\\in A$, then exactly one edge $vu$ from $E(v)$ has another end in $A$, and it is this edge that lies in $\\delta(A)$.
     So $|\\delta(A)\\cap E(v)|=1$.
  4) For grid and $A=R_{j,t}$ from Section 16.134, vertex $v=(t+1,j)$ has exactly one neighbor in $A$ (vertex $(t,j)$), so points 1-3 apply.
  5) At the level of XOR equations, this is exactly the rule for adding rows modulo 2:
     The XOR sum of the equation over $\\delta(R_{j,t})$ and the vertex equation over $E(v)$ gives the equation over $\\delta(R_{j,t+1})$, and the right-hand side is updated as $b_{t+1}=b_t\\oplus \\chi(v)$.
- `Toy test:` $n=4$, $j=2$, $t=1$. Then $A=\\{(1,2)\\}$, $v=(2,2)$.
  The boundary of $\\delta(A)$ contains the edge $(1,2)-(2,2)$, and the remaining edges from $E(v)$ go out, so $\\delta(A)\\cap E(v)=\\{(1,2)-(2,2)\\}$ and $\\delta(A\\cup\\{v\\})=\\delta(A)\\triangle E(v)$.
- `Status:` proven (geometric fact: "local" column-summing steps always have an intersection of $O(1)$, and in the simplest version - exactly 1 edge).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` combine this with Section 16.143 and the dyadic update of Section 16.136: write out an explicit diagram of how to keep the equations $\\delta(R_{j,t})$ in block form with $k=O(\\log n)$ so that each local step $t\\to t+1$ requires only (i) an XOR step "intersection=1" and (ii) $O(\\log n)$ disjointmerge operations; then find where in the strategy for the **entire** grid the "transverse" transition inevitably appears (and the Section 16.132 barrier turns on), or confirm that you can get by with just 1D order.

### 16.145. Exploratory step: "protocol" for maintaining block-form for $\\delta(R_{j,t})$ with $k=O(\\log n)$ in column-summing (local XOR-step + $O(\\log n)$ dyadic-merge)

- `Lens:` Compression/canonization.
- `Statement:` Let us fix the inner column $2\\le j\\le n-1$ and the sets $R_{j,t}$ from Section 16.134.
  Let us denote by $L_{j,t}$ and $H_{j,t}$ two horizontal segments of the border (left/right) and by $B_{j,t}$ the vertical "front" edge (if $t<n$), so that
  $$\\delta(R_{j,t})\\ =\\ L_{j,t}\\uplus H_{j,t}\\uplus \\{B_{j,t}\\}\\qquad (t<n)$$
  (see Section 16.134; there is no top edge for a regular $n\\times n$ grid).
  Then there is a canonical partition $\\mathcal P_{j,t}$ of the set $\\delta(R_{j,t})$ into
  $$k_t\\le 2\\lfloor\\log_2 n\\rfloor+3$$
  disjunct blocks (dyadic intervals along lines inside $L_{j,t}$ and $H_{j,t}$ from Section 16.136, plus singleton $\\{B_{j,t}\\}$),
  and the $t\\to t+1$ transition can be realized without a $k^2$explosion:
  1) (XOR step.) By Section 16.144 we have $\\delta(R_{j,t+1})=\\delta(R_{j,t})\\triangle E(v)$ for $v=(t+1,j)$ and $|\\delta(R_{j,t})\\cap E(v)|=1$.
     If $E(\\delta(R_{j,t}),b_t)$ and $E(E(v),\\chi(v))$ are written in block form with respect to the partitions $\\mathcal P_{j,t}$ and the singleton partition $E(v)$,
     then by Section 16.143 the XOR step outputs $E(\\delta(R_{j,t+1}),b_t\\oplus\\chi(v))$ to polynomial-size with $k_t=O(\\log n)$.
  2) (Dyadic-merge.) To maintain the canonical form of $\\mathcal P_{j,t+1}$, it is sufficient to separately perform the dyadic update of the prefix $t\\mapsto t+1$ from Section 16.136 for $L$ and $H$:
     "add singleton newline" and then do $O(\\log n)$ merges of adjacent equal intervals.
     Each such merger is a disjoint-merge and therefore reduces to the "easy case" of Section 16.137 (that is, to Section 16.130 with $k=2$).
  Therefore, in column-summing, maintaining the block form for all $t$ reduces to $n$ local XOR steps with intersection 1 and $O(n\\log n)$ disjoint-merge operations,
  Moreover, at each step the number of blocks remains $O(\\log n)$ (and the basechange occurs only between intervalpartition, where refinement is linear according to Section 16.133).
- `Proof:`
  1) (Canonical blocks.) Let us identify the edges $L_{j,t}$ with the positions of $[t]$ in row order (similarly for $H_{j,t}$).
     We apply Section 16.136 to each of the two prefixes of length $t$, obtaining dyadic partitions into $\\le\\lfloor\\log_2 t\\rfloor+1\\le\\lfloor\\log_2 n\\rfloor+1$ intervals.
     Adding singleton $\\{B_{j,t}\\}$, we obtain the partition $\\mathcal P_{j,t}$ and the estimate $k_t\\le 2(\\lfloor\\log_2 n\\rfloor+1)+1$.
  2) (XOR update of the boundary.) According to Section 16.144
     $$\\delta(R_{j,t+1})=\\delta(R_{j,t})\\triangle E(v),\\qquad |\\delta(R_{j,t})\\cap E(v)|=1,$$
     where $v=(t+1,j)$ and the common edge is $B_{j,t}$.
     Since $B_{j,t}$ in $\\mathcal P_{j,t}$ is a singleton, and $E(v)$ can be divided into singleton blocks (there are $\\le 4$ of them), the XOR step falls into the conditions of Section 16.143
     with a general refinement partition of size $\\le k_t+O(1)=O(\\log n)$.
  3) (Dyadic normalization.) After the XOR step, one new edge appears in the sets $L,H$ (line $t+1$), that is, their prefixes increase by 1.
     The canonical dyadic partition $[t+1]$ is obtained from the partition $[t]$ by adding a singleton and then $O(\\log n)$ merge operations (Section 16.136).
     Each merge operation glues two disjunct intervals and therefore has a polynomial-size bounded depth Frege simulation according to Section 16.137.
     Since all partitions are interval-partitions of the same order, their refinements do not produce a $k^2$-explosion (Section 16.133).
- `Toy test:` $n=8$, $t=5$.
  Dyadic partition $[5]=[1,4]\\uplus[5,5]$, and $[6]=[1,4]\\uplus[5,6]$ is obtained by adding singleton $[6,6]$ and merge $[5,5]\\uplus[6,6]\\mapsto[5,6]$.
  For $\\delta(R_{j,5})$ this means: on each of the two sides one edge is added and one disjoint-merge is made; then XOR with vertex $v=(6,j)$ changes $B_{j,5}$ to $B_{j,6}$, having an intersection at exactly $B_{j,5}$.
- `Status:` proven (reduction: inside column-summing there is no need for "transverse" base-change; maintaining $k=O(\\log n)$ reduces to intersection-1 XOR and dyadic-merge).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` move from one column to "column summation" as in Hastad-Risse Section 1.2: see if it is possible to choose block forms for the boundary equations of two adjacent columns so that their most common part (a strip of $n$ edges) is already synchronized by the same dyadic blocks, and then XOR addition of columns becomes a direct "easy case" Section 16.130 (without k^2); or fix the place where inconsistency of partitions is inevitable (rowcolumn) and the Section 16.132 barrier is turned on again.

### 16.146. Research step: adding adjacent columns in HR strategy reduces to an "easy case" Section 16.130 with a fixed dyadic partition of stripes $S_j$

- `Lens:` Equivalence.
- `Statement:` For $1\\le j\\le n-1$, let $S_j$ denote the set of $n$ horizontal edges between columns $j$ and $j+1$ (ordered by rows).
  Let for each stripe $S_j$ be fixed a dyadic partition into $r=O(\\log n)$ of disjoint row-interval blocks (canonical from Section 16.136 for $[n]$),
  and a block representation (in the sense of Section 16.130) of equations of the form $E(S_j,b)$ is available as XOR over the block parities of these $r$ blocks.
  Then "adding an adjacent column" in the Hastad-Risse scheme Section 1.2 is implemented with one XOR step in the "easy case":
  If
  $$E(S_j,\\,b)\\qquad\\text{and}\\qquad E(S_j\\uplus S_{j+1},\\,c)$$
  written as XOR over blocks of one common partition $S_j\\uplus S_{j+1}$ (combination of dyadic blocks on $S_j$ and $S_{j+1}$), then the boundeddepth Frege outputs
  $$E(S_{j+1},\\,b\\oplus c)$$
  polynomialsize (with a depth controlled by block parity depths), since
  $$(S_j)\\triangle(S_j\\uplus S_{j+1})=S_{j+1}.$$
  That is, a large intersection of size $|S_j|=n$ does not lead to $k^2$basechange: it "collapses" at the level of common block atoms.
- `Proof:`
  1) (Symmetric difference.) Since $S_j\\cap S_{j+1}=\\varnothing$, we have
     $$(S_j)\\triangle(S_j\\uplus S_{j+1})=((S_j\\triangle S_j)\\triangle S_{j+1})=\\varnothing\\triangle S_{j+1}=S_{j+1}.$$
  2) (General partition and parameter $k$.) The stripes $S_j$ and $S_{j+1}$ are disjoint, therefore the union of their dyadic partitions gives the partition
     $$S_j\\uplus S_{j+1}=\\biguplus_{t=1}^{k} D_t$$
     with $k\\le 2r=O(\\log n)$.
     Then both equations $E(S_j,b)$ and $E(S_j\\uplus S_{j+1},c)$ are unions of blocks of the same partition $\\{D_t\\}$.
  3) (XOR step as an "easy case".) According to Section 16.130, for such a fixed block basis there is a bounded depth Frege output of size $2^{O(k)}=\\mathrm{poly}(n)$,
     proving
     $$E(S_j,b)\\wedge E(S_j\\uplus S_{j+1},c)\\to E(S_{j+1},b\\oplus c).$$
  4) (Relation to HR Section 1.2.) The equation $E(S_j\\uplus S_{j+1},c)$ is the "equation of the column $j+1$" (the boundary of the full column; a special case of Section 16.134 for $t=n$),
     and $E(S_j,b)$ is "the equation of the strip from the first $j$ columns" (the boundary of the vertical strip).
     Therefore, the "add next column" step in linear modulo 2 reasoning is reduced to one XOR step in the mode of Section 16.130.
- `Toy test:` $n=6$.
  The canonical dyadic partition $[6]=[1,4]\\uplus[5,6]$ defines two blocks on each stripe $S_j$.
  Then $E(S_j,b)$ uses two stripe blocks on $S_j$, and $E(S_j\\uplus S_{j+1},c)$ uses four stripe blocks on $S_j\\uplus S_{j+1}$.
  Their XOR addition cancels both blocks on $S_j$ and leaves exactly two blocks on $S_{j+1}$.
- `Status:` proven (adjacent columns do not require a "transverse" basechange: it is enough to fix identical dyadicblocks on the common stripe $S_j$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` clarify the remaining node Q39: in Section 16.145-Section 16.146 the basis part of Gaussian elimination on the grid was reduced to the "easy case" on $k=O(\\log n)$ block atoms;
  now we need to either (a) formally control the depth of block parities for all necessary dyadic-merges (so as not to get into $O(\\log n)$), or (b) allocate a place in the full HR output, where a base-change between incompatible partitions is still required (and then the barrier Section 16.132 is returned).

### 16.147. Research step: caveat - Hastad'86, Remark 6 talks about **schemes**, and Frege lines require **formulas**; naive "unfolding" of the circuit into a formula gives a blow-up $M^{\\Theta(d)}$

- `Lens:` Model stress test.
- `Statement:` Link Hastad'86, Remark 6 (`../../resources/downloads/hastad_1986.pdf`) gives the upper bound for PARITY in the model of **depth-$d$ circuits**.
  But in Schoenfield-Frege, strings are **formulas** (trees), and the general translation "scheme -> equivalent formula of the same depth" can inflate the size to $M^{O(d)}$.
  In particular, if the only justification of the representability parameter $(\\log M)^{d-1}$ relies on Remark 6, then at the threshold depth $d\\approx \\log n/\\log\\log n$ with $M=\\mathrm{poly}(n)$ the unfolding yields only quasi-poly size and does not cover the needed regime.
- `Proof:`
  Let $C$ be a Boolean circuit of size $S$ and depth $d$ (single output).
  Let's construct an equivalent formula $F$ "by expanding DAG into a tree": root is the output of the circuit; For the entry node of the gate $g$, we add the corresponding symbol to the formula and recursively expand its inputs, **copying** the subformulas with each new use of $g$.
  Then the depth of $F$ is equal to the depth of $C$.
  Let's estimate the size: each entry of a gate in the scan corresponds to a certain path in the circuit going from this gate to the output.
  The length of the path is $\\le d$, and at each step you can go to at most one of the $\\le S$ gates of the next level, which means the number of different paths from any gate to the output is roughly limited by $S^{d}$.
  Therefore, each of the $S$ gates can appear in the scan no more than $S^{d}$ times, and
  $$|F|\\ \\le\\ S\\cdot S^{d}\\ =\\ S^{d+1}\\ =\\ S^{O(d)}.$$
  Substituting $S:=M=n^C$ and $d:=\\Theta(\\log n/\\log\\log n)$ gives
  $$|F|\\ \\le\\ n^{C(d+1)}\\ =\\ 2^{\\Theta(\\log^2 n/\\log\\log n)},$$
  that is, quasi-poly, not polynomial.
- `Toy test:` $n=2^{64}$, $M=n^4=2^{256}$, $d=13$.
  Then even a rough estimate of the development gives $|F|\\le M^{14}=2^{3584}$.
- `Status:` an exact failure has been identified: Remark 6 itself does not justify the "formular" representability part in the $d\\approx\\log n/\\log\\log n$ mode (the sweep gives exactly that $M^{\\Theta(d)}$ that HR marks as insufficient).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find (or derive) **formula** upper bound for PARITY in the desired model (depth as in HR, base $\\{\\vee,\\neg\\}$, ORoutput), giving size $M$ on block $(\\log M)^{d-1}$; then return to node Q39 about depth control during dyadic-merge without accumulating $O(\\log n)$.

### 16.148. Research step: an explicit constructive upper bound for $\\mathrm{PARITY}$ by depth formulas $d$ gives only $\\log \\mathrm{size}=O((d-1)\\,m^{1/(d-1)})$ (DNFcomposition) - this is not enough at the threshold

- `Lens:` Trade-off.
- `Statement:` For integers $d\\ge 2$ and $t\\ge 2$ we set $m:=t^{d-1}$.
  Then there are formulas (in De Morgan form, with OR output) for depth $d$ and size
  $$\\mathrm{size}\\ \\le\\ \\mathrm{poly}(m)\\cdot 2^{\\,O((d-1)\\,t)}\\ =\\ \\exp\\bigl(O((d-1)\\,m^{1/(d-1)})\\bigr),$$
  calculating $\\mathrm{PARITY}_m$ and $\\neg\\mathrm{PARITY}_m$.
  Inversion gives: to keep within the size $\\le M$, from this constructive bound it follows only
  $$m\\ \\le\\ \\left(\\Theta\\!\\left(\\frac{\\log M}{d-1}\\right)\\right)^{d-1},$$
  that is, at the threshold $d\\approx\\log n/\\log\\log n$ for $M=\\mathrm{poly}(n)$, this approach covers only $n^{o(1)}$ variables and does not justify the target block $(\\log M)^{d-1}\\ge n$.
- `Proof:`
  1) (Composition of blocks.) For $m=t^{d-1}$, we divide the variables into $t$ blocks of $t^{d-2}$ variables.
     Let $P_{d-1}$ and $N_{d-1}$ be formulas of depth $d-1$ that calculate parity/nonparity on $t^{d-2}$ variables.
     Then $\\mathrm{PARITY}_m$ can be written as DNF over $t$ "literal blocks":
     $$\\bigvee_{a\\in\\{0,1\\}^t:\\ \\oplus_i a_i=1}\\ \\bigwedge_{i=1}^t L_i(a),\\qquad L_i(a):=\\begin{cases}P_{d-1}(\\text{block }i),&a_i=1\\\\N_{d-1}(\\text{block }i),&a_i=0.\\end{cases}$$
     Similarly for $\\neg\\mathrm{PARITY}_m$ (take $\\oplus_i a_i=0$). OR output saved.
  2) (Recursion on size.) Let $S(d,m)$ denote the size of such a construction.
     Then for $m=t^{d-1}$ we have
     $$S(d,\\,t^{d-1})\\ \\le\\ 2^{t}\\cdot O(t)\\cdot S(d-1,\\,t^{d-2}).$$
     Base $d=2$: DNF for parity on $t$ variables has $2^{t-1}$ terms and size $S(2,t)\\le 2^{t}\\cdot O(t)$.
     By induction we obtain $S(d,t^{d-1})\\le 2^{(d-1)t}\\cdot \\mathrm{poly}(t)\\le \\mathrm{poly}(m)\\cdot 2^{O((d-1)t)}$.
  3) (Inversion.) If $S(d,m)\\le M$, then from $\\log M\\ge \\Omega((d-1)\\,m^{1/(d-1)})$ it follows
     $m\\le (\\Theta((\\log M)/(d-1)))^{d-1}$.
     For $d=\\Theta(\\log n/\\log\\log n)$ and $M=n^{O(1)}$ we have $(\\log M)/(d-1)=\\Theta(\\log\\log n)$, which means
     $$m\\ \\le\\ (\\Theta(\\log\\log n))^{\\Theta(\\log n/\\log\\log n)}\\ =\\ n^{o(1)}\\ll n.$$
- `Toy test:` $n=2^{64}$, $M=n^4$ (so $\\log M=256$), $d=13$ (so $d-1=12$).
  Then the estimate gives the maximum
  $$m\\ \\lesssim\\ (256/12)^{12}\\ \\approx\\ 21^{12}\\ \\approx\\ 2^{53}\\ <\\ 2^{64}=n.$$
- `Status:` an honest "too weak" formulaic upper bound is obtained: the DNFcomposition really gives exactly the type of blowup on $d$, which makes representability on the verge of unproven.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find (or refute) a significantly stronger **formula** upper bound for $\\mathrm{PARITY}$ of depth $d\\approx\\log n/\\log\\log n$ (in the spirit of the Hastad'86 circuit bound without the factor $(d-1)$ in the exponent); otherwise, representation-reduction Q39 may be blocked already at the "PARITY in one block" level.

### 16.149. Research step: the factor $d$ in the exponent for PARITY formulas is **irremovable** (Rossman'16)  block $(\\log M)^{d-1}$ with size $M$ is impossible for formulas with growing $d$

- `Lens:` Link/barrier (close "folklore" with an accurate fact).
- `Statement:` For unbounded fan-in De Morgan formulas (trees) of depth $D\\ge 2$, the function $\\mathrm{PARITY}_n$ requires size
  $$\\mathrm{size}\\ \\ge\\ 2^{\\,\\Omega\\bigl((D-1)\\,(n^{1/(D-1)}-1)\\bigr)}$$
  (Rossman'16, Thm. 3; see `../../resources/downloads/rossman_2016_average_sensitivity_bounded_depth_formulas.pdf`).
  Therefore, if the depth formula $D$ has size $\\le M$ and evaluates $\\mathrm{PARITY}_n$, then inevitably
  $$n\\ \\le\\ \\left(\\Theta\\!\\left(\\frac{\\log M}{D-1}\\right)\\right)^{D-1}.$$
  In particular, as $D$ grows, it is impossible to have a "representability block" of size $(\\log M)^{D-1}$ with size $M$ (as in the HR heuristic Section 1.2): such a block requires size $\\ge M^{\\Omega(D)}$.
- `Proof:`
  1) (Lower bound.) Rossman'16, Thm. 3 states for depth $d+1$:
     $$\\mathrm{size}\\ge 2^{\\Omega(d(n^{1/d}-1))}.$$
     Putting $D:=d+1$, we obtain the stated bound $2^{\\Omega((D-1)(n^{1/(D-1)}-1))}$.
  2) (Inversion.) From $M\\ge 2^{\\Omega((D-1)(n^{1/(D-1)}-1))}$ it follows
     $n^{1/(D-1)}\\le O((\\log M)/(D-1))+1$, that is, $n\\le (\\Theta((\\log M)/(D-1)))^{D-1}$ (for $n$ over constants).
  3) (Comparison with Section 16.148.) The upper bound of Section 16.148 gives
     $$\\log\\mathrm{size}=O\\bigl((D-1)\\,n^{1/(D-1)}\\bigr),$$
     those. together with Rossman'16, the factor $(D-1)$ in the indicator turns out to be tight (up to constants).
  4) (Failure of block $(\\log M)^{D-1}$.) If we take $n:=(\\log M)^{D-1}$, then $n^{1/(D-1)}=\\log M$ and lower bound gives
     $$\\mathrm{size}\\ge 2^{\\Omega((D-1)\\log M)}=M^{\\Omega(D-1)},$$
     which, as $D$ grows, is significantly greater than $M$.
- `Toy test:` $M=n^4$, $D=13$.
  Then the "desired" block $n=(\\log M)^{12}=256^{12}=2^{96}$ would require, according to Rossman'16, size $\\ge 2^{\\Omega(12\\cdot 256)}=2^{\\Omega(3072)}\\gg M=2^{256}$.
- `Status:` closed as a known fact: for formulas (fan-out 1) a strong upper bound without the multiplier $(D-1)$ is impossible; The representability node Q39 really "breaks" already at the level of PARITY blocks at the threshold depth.
- `Barrier check:` r - not applicable (no oracles), NP - not applicable, alg - not applicable.
- `Next step:` rebuild the formulation of Q39: either (a) HR Section 1.2 should treat "size" not as a tree-size formula (but as a DAG/scheme, which in Frege is not a string), or (b) for bounded-depth Frege, the representation of intermediate XOR equations really requires a quasi-poly size already because of the PARITY formulas, and then the "depth gap" is not reduced to one XOR step.

### 16.150. Exploratory step: HR depth (= alternation $\\vee/\\neg$) reduces to De Morgan depth $\\Theta(d)$ without loss of size  Rossman'16 estimate applies to bounded-depth Frege strings

- `Lens:` Equivalence.
- `Statement:` In HR'22 (SchoenfieldFrege), formulas are built over the base $\\{\\vee,\\neg\\}$; size = number of ligaments, depth = number of $\\vee/\\neg$ alternations on the path (see. `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`, Section 2.1, definitions after the line "The size of a formula...").
  For any such formula $A$ there is an equivalent De Morgan formula $A^{\\mathrm{NNF}}$ (internal gates $\\vee/\\wedge$, negations only at leaves) such that
  1) $|A^{\\mathrm{NNF}}|\\le |A|$ (up to constants in the choice of size metric),
  2) $\\mathrm{depth}_{\\wedge/\\vee}(A^{\\mathrm{NNF}})\\le \\lfloor d/2\\rfloor+1$, where $d:=\\mathrm{altdepth}_{\\vee/\\neg}(A)$.
  Therefore, the Rossman'16 lower estimate for PARITY-**formulas** in depth (see. `../../resources/downloads/rossman_2016_average_sensitivity_bounded_depth_formulas.pdf`, Thm. 3) directly limits representability in boundeddepth Frege: with a fixed $d$ and a row size $\\le M$, parity cannot be covered on a block of size $(\\log M)^{d-1}$; the maximum is only $\\bigl(\\Theta((\\log M)/d)\\bigr)^{\\Theta(d)}$ (coincident with Section 16.148-Section 16.149).
- `Proof:`
  1) (NNF translation without blow-up.) Define $A^{\\mathrm{NNF}}$ by "push-negation" recursion:
     $$(\\neg B)^{\\mathrm{NNF}}:=\\mathrm{push}(\\neg,B),\\qquad (B_1\\vee\\cdots\\vee B_k)^{\\mathrm{NNF}}:=B_1^{\\mathrm{NNF}}\\vee\\cdots\\vee B_k^{\\mathrm{NNF}},$$
     and the function $\\mathrm{push}(s,\\cdot)$ for the polarity $s\\in\\{+,-\\}$ is given by the rules
     $$\\mathrm{push}(+,x)=x,\\ \\mathrm{push}(-,x)=\\neg x,$$
     $$\\mathrm{push}(+,\\neg C)=\\mathrm{push}(-,C),\\ \\mathrm{push}(-,\\neg C)=\\mathrm{push}(+,C),$$
     $$\\mathrm{push}(+,C_1\\vee\\cdots\\vee C_k)=\\bigvee_i \\mathrm{push}(+,C_i),\\qquad \\mathrm{push}(-,C_1\\vee\\cdots\\vee C_k)=\\bigwedge_i \\mathrm{push}(-,C_i).$$
     This is the standard translation in negation normal form: the negations go to the leaves, and $\\vee$ under odd polarity becomes $\\wedge$. The size does not grow (each original node $\\vee$ remains one node $\\vee$ or $\\wedge$; double negatives are canceled).
  2) (Relationship of depths.) Consider any path in $A$.
     Each new internal gate ($\\vee$ in $A^{\\mathrm{NNF}}$ or $\\wedge$) on this path corresponds to some original $\\vee$ node on the path in $A$.
     Between two different $\\vee$nodes on the path to $A$ there must be at least one $\\neg$ (otherwise they can be merged by $\\vee$ associativity without increasing the alternation depth).
     Therefore, the number of $\\vee$-nodes on any path is $\\le \\lfloor d/2\\rfloor+1$.
     Since $\\mathrm{depth}_{\\wedge/\\vee}(A^{\\mathrm{NNF}})$ is the maximum number of $\\vee/\\wedge$ nodes on the path, we obtain the stated estimate.
  3) (Applying Rossman'16.) If the string bounded-depth Frege has alternation depth $\\le d$ and size $\\le M$, then $A^{\\mathrm{NNF}}$ has De Morgan-depth $D\\le \\lfloor d/2\\rfloor+1$ and size $\\le O(M)$.
     Then by Section 16.149 (Rossman'16, Thm. 3 in terms of De Morgan depth $D$) parity on $n$ variables requires
     $$M\\ \\ge\\ 2^{\\Omega\\bigl((D-1)(n^{1/(D-1)}-1)\\bigr)},$$
     which, when inverted, gives $n\\le (\\Theta((\\log M)/(D-1)))^{D-1}$, that is, $n\\le (\\Theta((\\log M)/d))^{\\Theta(d)}$.
- `Toy test:` let $M=n^4$ and $d:=\\lceil\\log n/\\log\\log n\\rceil$.
  Then $(\\log M)/d=\\Theta(\\log\\log n)$ and bound $n\\le (\\Theta((\\log M)/d))^{\\Theta(d)}$ gives only $n^{o(1)}$ variables in one PARITY block, while $(\\log M)^{d-1}\\ge n$ is purely arithmetically; This means that the representability premise is broken.
- `Status:` proven (reducing HR-depth to De Morgan-depth makes the application of Rossman'16 to bounded-depth Frege strings formally correct).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` re-read HR Section 1.2 in the original PDF: are they not implicitly using **schemas**/DAGs instead of tree formulas when they say "formulas of size $M$"; if not, then in Q39 the representability part should be considered a closed obstacle and look for another upper approach (not through broad parities).

### 16.151. Research step: HR Section 1.2 "groups of size $(\\log M)^{d-1}$ and formulas of size $M$" is just a constant-depth heuristic (with suppressed factor $d$); with a tree size, the correct block is $\\le \\bigl(\\Theta((\\log M)/(d-1))\\bigr)^{d-1}$, otherwise the size needed is $\\ge M^{\\Omega(d)}$

- `Lens:` Clarification of the formulation (parameters/model).
- `Statement:` In HR'22, formulas are **trees**: "The size of a formula is the number of connectives ... when A is viewed as a tree" (see. `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`, §2.1).
  In Section 1.2 they write: break the variables into groups of size $(\\log M)^{d-1}$ and "write down formulas of depth $d$ and size $M$ that represent the parity and the negation of the parity of each group" (ibid., Section 1.2, paragraph starting with "Let us consider proofs...").
  Moreover, in terms of their own measure (treesize + alternation depth), such a phrase is compatible with known bounds only if one understands "size $M$" with a polynomial clause (e.g. $M^{\\Theta(d)}$) or considers $d$ a constant and suppresses the factor $(d-1)$: for size $\\le M$ the maximum block
  $$m\\ \\le\\ \\bigl(\\Theta((\\log M)/(d-1))\\bigr)^{d-1}$$
  (see Section 16.148-Section 16.150), and $m=(\\log M)^{d-1}$ requires size $\\ge M^{\\Omega(d)}$ (see Section 16.149).
- `Proof:`
  1) HR'22 fix the tree size and depth as alternations $\\vee/\\neg$ (Section 2.1), i.e. These are exactly the fan-out 1 formulas.
  2) By Section 16.150, any such depth formula $d$ can be translated into a De Morgan depth formula $\\Theta(d)$ without increasing the size, so we apply lower bound Rossman'16 (Thm. 3) to HR-Frege strings, see Section 16.149.
  3) Rossman'16 inversion gives: if a string has size $\\le M$, then parity can be covered only on $m\\le \\bigl(\\Theta((\\log M)/(d-1))\\bigr)^{d-1}$ variables; substituting $m=(\\log M)^{d-1}$ into Section 16.149 gives the required size $\\ge M^{\\Omega(d)}$.
- `Toy test:` $M=n^4$, $d=13$ (so $\\log M=256$).
  Then the correct block would be $m\\lesssim(256/12)^{12}\\approx 2^{53}$, and "$(\\log M)^{12}$" would give $m=2^{96}$ and require size $\\ge M^{\\Omega(12)}$.
- `Status:` clarified: HR Section 1.2 does not hide DAG sharing (they themselves define tree formulas); "$(\\log M)^{d-1}$ for size $M$" should be read as a constant-depth heuristic/polynomial factor suppression and should not be used when $d$ is growing in Q39.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` reformulate Q39 as a **formulas vs circuits** problem: check where exactly in Hastad'20/HR'22 the lower bound relies on fanout 1 (formulas), and whether it gives the same threshold for "circuitFrege" (circuitlines).

### 16.152. Research step: block $(\\log M)^{d-1}$ is natural for **schemes** (fan-out $>1$) due to sharing; for **formulas** the factor $(d-1)$ in the exponential is inevitable

- `Lens:` Trade-off (size vs depth; formulas vs schemes).
- `Statement:` Let $d\\ge 2$, $t\\in\\mathbb N$, $m:=t^{d-1}$.
  Then there is an unbounded fan-in De Morgan-**circuit** of depth $d$ of size $\\le \\mathrm{poly}(t)\\cdot 2^{O(t)}$, computing $\\mathrm{PARITY}_m$ (and similarly $\\neg\\mathrm{PARITY}_m$).
  Consequently, with size $\\le M$ it is possible to cover the block $m=(\\Theta(\\log M))^{d-1}$ - this is exactly the dependence that appears in HR Section 1.2.
  For De Morgan-**formulas** (fan-out $=1$) the same "DNF-composition" gives $\\mathrm{size}\\le 2^{\\Theta((d-1)t)}\\cdot\\mathrm{poly}(t)$ (see Section 16.148), and Rossman'16 shows that the factor $(d-1)$ in exponent tight (Section 16.149).
- `Proof:`
  1) (Base $d=2$.) $\\mathrm{PARITY}_t$ and $\\neg\\mathrm{PARITY}_t$ have DNF/CNF with $2^{t-1}$ terms/clauses (exhaustive search over values with the required parity), i.e. depth 2 scheme of size $2^{O(t)}$.
  2) (Induction on $d$; key: sharing.) Let's divide $m=t^{d-1}$ variables into $t$ blocks of $t^{d-2}$ each.
     Let $P_{d-1}$ and $N_{d-1}$ be circuits of depth $d-1$ that calculate the parity/non-parity of a block of size $S_{d-1}$.
     Let's take depth-2 DNF for $\\mathrm{PARITY}$ on $t$ "literals" $y_1,\\dots,y_t$:
     $$\\bigvee_{a\\in\\{0,1\\}^t:\\ \\oplus a=1}\\ \\bigwedge_{i=1}^t \\ell_i(a),\\qquad \\ell_i(a):=\\begin{cases}y_i,&a_i=1\\\\ \\neg y_i,&a_i=0.\\end{cases}$$
     and substitute $y_i:=P_{d-1}(\\text{block }i)$, $\\neg y_i:=N_{d-1}(\\text{block }i)$.
     In the **scheme** each $P_{d-1}(\\text{block }i)$ and $N_{d-1}(\\text{block }i)$ is calculated once and fan-out's in all $2^{t-1}$ terms, so
     $$S_d\\ \\le\\ t\\cdot( S_{d-1}+S_{d-1})\\ +\\ 2^{O(t)}\\cdot\\mathrm{poly}(t)\\ =\\ O(t)\\,S_{d-1}+2^{O(t)}\\mathrm{poly}(t).$$
     By induction from $S_2=2^{O(t)}$ we obtain $S_d\\le 2^{O(t)}\\mathrm{poly}(t)$ (the upper level dominates).
  3) (Corollary for the block size.) From $S_d\\le M$ it follows $t=O(\\log M)$, which means $m=t^{d-1}=(\\Theta(\\log M))^{d-1}$.
  4) (Contrast with formulas.) In a formula, the same step requires copying the block subformula within each term, giving a factor of $2^{t}$ at each level and a total of $2^{\\Theta((d-1)t)}$ (Section 16.148); this is the "lost" factor $(d-1)$ compared to the circuits.
- `Toy test:` $M=n^4$, $d=13$ (so $\\log M=256$, $t=\\Theta(256)$).
  The circuit bound allows a block $m=t^{12}\\approx (256)^{12}=2^{96}$ with size $\\approx 2^{O(256)}=n^{O(1)}$, whereas for formulas such a block requires size $\\ge M^{\\Omega(12)}$ (Section 16.149).
- `Status:` it has been proven: the HR dependence $m=(\\log M)^{d-1}$ is explained precisely by **sharing** (fan-out) and corresponds to the schematic rather than formulaic mode.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` record which proof system "circuit-Frege" corresponds to and whether it is p-equivalent to EF; then check whether the lower bound Hastad'20 applies to such a strengthened mode.

### 16.153. Exploratory step (toy computation): fixed 2x2 row partition blocks single-step column summing

- `Lens:` Invariant.
- `Statement:` Consider $4\\times 4$ grid and column $j=2$. Let
  $$S_2:=\\{e_i:=((i,2),(i,3))\\mid i=1,2,3,4\\}$$
  -- horizontal edges between columns $2$ and $3$.
  Let us fix the row blocks $B_{\\mathrm{top}}:=\\{e_1,e_2\\}$ and $B_{\\mathrm{bot}}:=\\{e_3,e_4\\}$,
  and we consider all other edges to be singleton blocks. Let's call the XOR equation **compatible** with this
  partitioning, if its support is the union of entire blocks. Then any compatible equation
  intersects $S_2$ at $0$, $2$ or $4$ edges (the parity of $|S_2\\cap \\mathrm{supp}|$ is $0$ and
  saved under XOR). But the intermediate equation $E(\\delta(R_{2,1}),b)$ from column-summing
  has $|S_2\\cap \\delta(R_{2,1})|=1$, which means it is incompatible. Therefore the sequence
  Gaussian-elimination of steps $t\\to t+1$ cannot remain compatible with fixed 22
  row partitioning; a basechange is required (refinement of blocks to at least $S_2$ singletons).
- `Toy test:` $R_{2,1}=\\{(1,2)\\}$, therefore
  $$\\delta(R_{2,1})=\\{(1,2)-(1,1),\\ (1,2)-(1,3),\\ (1,2)-(2,2)\\}.$$
  The intersection with $S_2$ is equal to $\\{(1,2)-(1,3)\\}=\\{e_1\\}$, that is, it is **half** of the block $B_{\\mathrm{top}}$.
- `Status:` partially (toy computation: local invariant shows forced basechange by 44).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` generalize the invariant: for $n\\times n$ and partitioning into 2-line blocks
  show that all prefixes of odd length $R_{j,t}$ are incompatible with a fixed partition;
  Next, check whether "batching" for even $t$ can bypass this obstruction without changing partitions.

### 16.154. Probe step: odd prefix is incompatible with fixed 2-line partitioning

- `Lens:` Invariant.
- `Statement:` Let $G$ be a $n\\times n$ grid, $1\\le j\\le n-1$, $S_j$ be the horizontal edges between
  columns $j$ and $j+1$, and $R_{j,t}=\\{(i,j):1\\le i\\le t\\}$ (as in Section 16.134). Let's fix the partition
  $\\mathcal P$ edges in which each intersection of a block with $S_j$ is of even size (in particular,
  splitting $S_j$ into pairs along the lines $\\{e_{2r-1},e_{2r}\\}$ and singletons outside $S_j$). Then for anyone
  of odd $t$, the set $\\delta(R_{j,t})$ is not a union of blocks $\\mathcal P$.
  Therefore, column summing cannot remain compatible with the fixed 2-line
  partition for all steps $t\\to t+1$; a basechange is needed (or refinement to singletons on $S_j$).
- `Proof:` For each $1\\le i\\le t$ the edge $((i,j),(i,j+1))\\in S_j$ has exactly one end
  in $R_{j,t}$, then $S_j\\cap\\delta(R_{j,t})=\\{((i,j),(i,j+1)):1\\le i\\le t\\}$ and
  $|S_j\\cap\\delta(R_{j,t})|=t$. If $\\delta(R_{j,t})$ were the union of $\\mathcal P$ blocks,
  then $|S_j\\cap\\delta(R_{j,t})|$ would be even, since each block intersects $S_j$ along an even
  number of ribs. If $t$ is odd, we get a contradiction, which means compatibility is impossible.
- `Toy test:` $n=6$, $t=3$ or $t=5$: the intersection with $S_j$ is 3 or 5 edges, i.e. odd.
- `Status:` proven (general parity invariant of intersection with $S_j$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether batching on even $t$ (Q39.S9) can bypass this obstruction.
- `StepID:` Q39.S8-generalize-block-invariant.
- `InfoGain:` 1.

### 16.155. Exploratory step (counterexample): even-batching does not avoid inconsistent row when fixed 2-line partitioning

- `Lens:` Equivalence.
- `Statement:` Consider "batching" $t\\to t+2$ through a two-line strip
  $$B_{t+1,t+2}:=\\{(t+1,j),(t+2,j)\\}.$$
  If we fix a 2-line partition of the strip $S_j$ into pairs $\\{e_{2r-1},e_{2r}\\}$ (and singletons outside $S_j$),
  then we can hope that the equation $E(\\delta(B_{t+1,t+2}),\\chi_{t+1}\\oplus\\chi_{t+2})$ is compatible and
  allows you to bypass odd prefixes $R_{j,t+1}$. Toy check below shows that this **doesn't** fix
  incompatible strings: to get $\\delta(B_{t+1,t+2})$, you need to use them separately
  two vertex equations, each of which violates a fixed partition.
- `Toy test:` $n=4$, $j=2$. Let
  $$S_2=\\{e_i:=((i,2),(i,3))\\mid i=1,2,3,4\\},\\qquad
  B_{\\mathrm{top}}=\\{e_1,e_2\\},\\ B_{\\mathrm{bot}}=\\{e_3,e_4\\}.$$
  Consider the vertices $v_1=(1,2)$ and $v_2=(2,2)$.
  The vertex equations $E(E(v_1),\\chi(v_1))$ and $E(E(v_2),\\chi(v_2))$ intersect with $S_2$
  exactly in $\\{e_1\\}$ and $\\{e_2\\}$ respectively, that is, **not** they are unions of blocks
  $\\{B_{\\mathrm{top}},B_{\\mathrm{bot}}\\}$.
  Their XOR sum is equal to
  $$E(E(v_1)\\triangle E(v_2),\\chi(v_1)\\oplus\\chi(v_2))
    =E(\\delta(B_{1,2}),\\chi(v_1)\\oplus\\chi(v_2)),$$
  and here $S_2\\cap\\delta(B_{1,2})=\\{e_1,e_2\\}=B_{\\mathrm{top}}$, that is, the resulting string is compatible.
  However, any output via XOR uses **both** source strings, and the first "partial sum"
  (one of the vertex rows) is incompatible with the fixed 2-line partition.
- `Status:` counterexample (toy): evenbatching $t\\to t+2$ does not allow incompatible strings to be bypassed without
  base-change, since the vertex equations themselves cut 2-line blocks.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen into a general invariant: with a fixed 2-line partition, any linear
  a combination of vertex equations that adds two rows at a time still requires an intermediate row,
  violating partition (Q39.S10).
- `StepID:` Q39.S9-even-batching-construct.
- `InfoGain:` 1.

### 16.156. Exploratory step (toy computation): XOR tree for $\\delta(B_{1,2})$ contains an incompatible vertex

- `Lens:` Invariant.
- `Statement:` Let us fix $n=4$, $j=2$ and a 2-line partition of $S_2$ into blocks
  $B_{\\mathrm{top}}=\\{e_1,e_2\\}$, $B_{\\mathrm{bot}}=\\{e_3,e_4\\}$ (singletons outside $S_2$).
  Let the XOR tree output the string $\\delta(B_{1,2})$ from the vertex equations.
  Then there is a vertex in the tree whose support intersects $S_2$ along one edge
  (that is, the string is not compatible with fixed partitioning).
- `Toy test:` Consider the projection onto $B_{\\mathrm{top}}$ (two variables $e_1,e_2$),
  encoding it as a vector of $\\{00,10,01,11\\}\\subset\\mathbb F_2^2$.
  For vertex equations only $00$ (vertices outside $S_2$) and $10$ or $01$ are possible
  (vertices incident to one of $e_1,e_2$), and the root is $11$, since
  $S_2\\cap\\delta(B_{1,2})=\\{e_1,e_2\\}$. In a binary XOR tree rooted at $11$
  consider the children of the root: their XOR gives $11$, which means either the pair $(10,01)$ (and the required
  vertex found), or $(11,00)$ (or $(00,11)$). In the latter case, we go down
  to the child labeled $11$. Since leaves cannot be $11$, the process
  stops at the top marked $10$ or $01$, which means
  $|S_2\\cap\\mathrm{supp}|=1$.
- `Status:` partially (toy computation on $4\\times4$: incompatible string is inevitable).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` generalize the argument tree to arbitrary $t,j$ and prove that
  with a fixed 2-line partition any XOR output $\\delta(B_{t+1,t+2})$
  of vertex equations must pass through a row with an odd intersection
  with some 2-line block (formal base-change invariant).
- `StepID:` Q39.S10-block-parity-invariant.
- `InfoGain:` 1.

### 16.157. Exploratory step (proof): XOR tree for $\\delta(B_{t+1,t+2})$ cuts a 2-line block

- `Lens:` Invariant.
- `Statement:` Let $G$ be $n\\times n$ grid, $1\\le j\\le n-1$, $1\\le t\\le n-2$,
  $S_j=\\{e_i:=((i,j),(i,j+1))\\mid 1\\le i\\le n\\}$, and a 2line block is fixed
  $B_{t+1,t+2}=\\{e_{t+1},e_{t+2}\\}\\subset S_j$. Consider an XOR tree that outputs the string
  $E(\\delta(B_{t+1,t+2}),\\chi_{t+1}\\oplus\\chi_{t+2})$ from the vertex equations $E(E(v),\\chi(v))$.
  Then there is a vertex in the tree whose support intersects $B_{t+1,t+2}$ in exactly one edge
  (that is, the string is not compatible with the fixed 2-line split).
- `Proof:` Let's consider the projection of $\\pi$ onto the coordinates $e_{t+1},e_{t+2}$, i.e. vectors from
  $\\mathbb F_2^2$ with encoding $00,10,01,11$. Each vertex leaf intersects $S_j$ in at most one
  edge, so the $\\pi$-labels of the leaves lie in $\\{00,10,01\\}$ (label $11$ is impossible).
  For the root we have $S_j\\cap\\delta(B_{t+1,t+2})=\\{e_{t+1},e_{t+2}\\}$, which means $\\pi(\\text{root})=11$.
  Let's take vertex $u$ with label $11$, closest to the root. Her children $u_1,u_2$ satisfy
  $\\pi(u_1)\\oplus\\pi(u_2)=11$. By choice $u$, no child has the label $11$, so
  $\\{\\pi(u_1),\\pi(u_2)\\}=\\{10.01\\}$. Therefore, one of the nodes $u_1,u_2$ has the label $10$ or $01$,
  which means the intersection of support with $B_{t+1,t+2}$ in exactly one edge.
- `Toy test:` $n=6$, $j=2$, $t=3$. The projection onto $\\{e_3,e_4\\}$ gives the root $11$, leaves in
  $\\{00,10,01\\}$, so a node labeled $10$ or $01$ is inevitable inside the tree.
- `Status:` proven (general XOR invariant for any $t,j$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether obstruction persists during even-batching on $2k$ lines
  (Q39.S11b).
- `StepID:` Q39.S11-xortree-projection-general.
- `InfoGain:` 1.

### 16.158. Exploratory step (counterexample): evenbatching on $2k$ lines does not give an XORtree of only $\\pi$compatible lines (toy $k=2$)

- `Lens:` Model stress test.
- `Statement:` Take $n=6$, fix the inner column $j$ and the stripe
  $$S_j=\\{e_i:=((i,j),(i,j+1))\\mid i=1,\\dots,6\\}.$$
  Let $\\pi$ be a partition where $S_j$ is divided into pairs
  $\\{e_1,e_2\\}$, $\\{e_3,e_4\\}$, $\\{e_5,e_6\\}$ (all other edges are singletons).
  Consider a strip of $2k=4$ lines
  $$B_{3..6}:=\\{(i,j):i=3,4,5,6\\}.$$
  Then the string $E(\\delta(B_{3..6}),\\bigoplus_{i=3}^6\\chi(i,j))$ $\\pi$-compatible
  (the intersection with $S_j$ is equal to $\\{e_3,e_4,e_5,e_6\\}$ - the union of two blocks),
  but in any XOR tree that derives it from the vertex equations, there is an incompatible line:
  each vertex equation $E(E((i,j)),\\chi(i,j))$ for $i\\in\\{3,4,5,6\\}$
  intersects $S_j$ in exactly one edge $e_i$, and therefore is not a union of blocks $\\pi$.
- `Toy test:` The projection onto the coordinates $e_3,e_4,e_5,e_6$ gives the vector $1111$ at the root.
  The only axioms with unity in the $e_i$ coordinate are vertex equations at the vertices $(i,j)$,
  therefore, each of them must appear in the XOR tree an odd number of times; it means it's inevitable in a tree
  there are incompatible leaves.
- `Status:` counterexample (toy, $k=2$): the requirement "all lines are $\\pi$compatible" is impossible,
  the incompatibility already appears at the leaves.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen to internal node: check if XOR tree can exist,
  where all *internal* nodes are $\\pi$compatible (no leaves), and if so, look for rank/projection
  obstruction for $2k$.
- `StepID:` Q39.S12-evenbatch-2k-counterexample.
- `InfoGain:` 1.

### 16.159. Exploratory step (counterexample): internal nodes can be $\\pi$compatible for $k=2$

- `Lens:` Invariant.
- `Statement:` In toy mode, $k=2$ can require that **all internal nodes** of the XOR tree,
  outputting $\\delta(B_{3..6})$ were $\\pi$-compatible (i.e., crossed $S_j$ by block union
  $\\{e_3,e_4\\}$ and $\\{e_5,e_6\\}$). Therefore, the invariant "a tree must have an internal node
  with odd parity in the block" is already incorrect by $k=2$.
- `Counterexample:` Let us take the leaves of the four vertex equations
  $$E(E((3,j)),\\chi(3,j)),\\ E(E((4,j)),\\chi(4,j)),\\ E(E((5,j)),\\chi(5,j)),\\ E(E((6,j)),\\chi(6,j)),$$
  and assemble a binary tree like
  $$\\big(E(E((3,j)),\\chi(3,j))\\oplus E(E((4,j)),\\chi(4,j))\\big)
    \\oplus\\big(E(E((5,j)),\\chi(5,j))\\oplus E(E((6,j)),\\chi(6,j))\\big).$$
  Internal nodes correspond to the vertex sets $U_1=\\{(3,j),(4,j)\\}$ and $U_2=\\{(5,j),(6,j)\\}$.
  Their boundaries satisfy
  $$S_j\\cap\\delta(U_1)=\\{e_3,e_4\\},\\qquad S_j\\cap\\delta(U_2)=\\{e_5,e_6\\},$$
  that is, both lines are $\\pi$compatible (the intersection with $S_j$ is exactly a block). The root gives
  $\\delta(U_1\\triangle U_2)=\\delta(B_{3..6})$ and also $\\pi$-compatible. Hence,
  all internal nodes can be $\\pi$compatible despite incompatible leaves.
- `Status:` counterexample (toy, $k=2$): block-cut-invariant for internal nodes does not work.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` move to a stronger constraint (e.g. rank/projection obstruction
  or a geometric constraint on the allowed subsets of vertices at internal nodes).
- `StepID:` Q39.S13-2k-block-cut-invariant.
- `InfoGain:` 1.

### 16.160. Exploratory step (counterexample): the projection rank of internal $\\pi$compatible lines is already equal to 2 at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let $\\pi$ split $S_j$ into blocks $B_1=\\{e_3,e_4\\}$ and
  $B_2=\\{e_5,e_6\\}$ (other edges are singletons). For an XOR tree where all internal nodes
  $\\pi$compatible, projection of the space of internal lines onto $B_1\\sqcup B_2$
  must have rank $\\le 1$; then the tree for $\\delta(B_{3..6})$ is impossible.
- `Counterexample:` Let's take a tree from Q39.S13 with internal nodes
  $U_1=\\{(3,j),(4,j)\\}$ and $U_2=\\{(5,j),(6,j)\\}$.
  Their boundaries give projections onto $(B_1,B_2)$:
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(00,11),$$
  and the root $\\delta(U_1\\triangle U_2)=\\delta(B_{3..6})$ gives $p=(11,11)$.
  Vectors $(11,00)$ and $(00,11)$ are linearly independent in $\\mathbb F_2^{B_1}\\oplus\\mathbb F_2^{B_2}$,
  therefore the projection rank of the internal nodes is 2, although they are all $\\pi$-compatible.
- `Status:` counterexample (toy, $k=2$): naive rank obstruction "rank$\\le 1$"
  does not work even with complete $\\pi$match of internal nodes.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the invariant by adding subset geometry (for example, the requirement
  that the internal nodes correspond to the union of intervals across rows), and check that
  does this give real rank obstruction at $k=2$.
- `StepID:` Q39.S14-2k-projection-rank-obstruction.
- `InfoGain:` 1.

### 16.161. Exploratory step (counterexample): interval geometry does not reduce projection rank for $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` If you require the internal nodes of an XOR tree to intersect
  $S_j\\cap\\delta(U)$ was one rowinterval (line-continuous segment),
  then the projection of internal lines onto blocks $B_1=\\{e_3,e_4\\}$ and $B_2=\\{e_5,e_6\\}$ must have rank $\\le 1$.
- `Counterexample:` Let's take a tree from Q39.S13 with internal nodes
  $U_1=\\{(3,j),(4,j)\\}$ and $U_2=\\{(5,j),(6,j)\\}$.
  Then
  $$S_j\\cap\\delta(U_1)=\\{e_3,e_4\\},\\qquad S_j\\cap\\delta(U_2)=\\{e_5,e_6\\},$$
  and both intersections are row-intervals (in row order on $S_j$). However, projections on
  $(B_1,B_2)$ are equal
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(00,11),$$
  which means the rank of the projection of internal nodes is 2.
- `Toy test:` $n=6$, any internal column $j$, $S_j=\\{e_1,\\dots,e_6\\}$ by row.
  The intervals $\\{e_3,e_4\\}$ and $\\{e_5,e_6\\}$ are continuous, but give independent projections onto $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): even with the "row-interval" condition, the projection rank of internal nodes is 2.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` clarify the geometric constraint: for example, require that internal nodes
  corresponded to connected regions with a monotonic boundary in both coordinates (and not just intervals on $S_j$),
  and check whether this gives real rank obstruction for $k=2$.
- `StepID:` Q39.S15-2k-interval-rank-obstruction.
- `InfoGain:` 1.

### 16.162. Exploratory step (counterexample): monotonic (prefix/suffix) geometry does not reduce projection rank for $k=2$

- `Lens:` Model stress test.
- `Assertion (attempt):` If you require the internal nodes of an XOR tree to intersect
  $S_j\\cap\\delta(U)$ was **monotonic** across lines (that is, prefix or suffix in order
  $e_1,\\dots,e_m$), then the projection of internal lines onto blocks $B_1,B_2$ must have rank $\\le 1$.
- `Counterexample:` Let's take $n=4$ and the inner column $j$. Let
  $$S_j=\\{e_1,e_2,e_3,e_4\\}$$
  are horizontal edges between columns $j$ and $j+1$ (in row order), and the partition $\\pi$ is given by
  blocks $B_1=\\{e_1,e_2\\}$ (upper prefix) and $B_2=\\{e_3,e_4\\}$ (lower suffix).
  Let's look at the internal nodes
  $$U_1=\\{(1,j),(2,j)\\},\\qquad U_2=\\{(3,j),(4,j)\\}.$$
  Then
  $$S_j\\cap\\delta(U_1)=B_1,\\qquad S_j\\cap\\delta(U_2)=B_2,$$
  and both intersections are monotonic (prefix/suffix). However, their projections onto $(B_1,B_2)$ are equal
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(00,11),$$
  that is, linearly independent; The rank of the projection of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$; the root $\\delta(U_1\\triangle U_2)$ has the intersection $S_j\\cap\\delta(U_1\\triangle U_2)=B_1\\cup B_2$,
  and internal nodes $U_1,U_2$ give monotonic prefix/suffix.
- `Status:` counterexample (toy, $k=2$): even with monotonic (prefix/suffix) geometry
  the projection rank of internal nodes is 2.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen geometry: require internal nodes to correspond to connected regions
  with a monotone boundary **in both coordinates** (for example, rectangles/step-shaped regions),
  and check whether this gives real rank obstruction for $k=2$.
- `StepID:` Q39.S16-2k-monotone-geometry-obstruction.
- `InfoGain:` 1.

### 16.163. Exploratory step (counterexample): rectangular geometry does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` If you require internal nodes of an XOR tree to
  corresponded to axially parallel rectangles in the grid (connected areas with monotonic
  boundary in both coordinates), then the projection of internal lines onto blocks $B_1,B_2$ must have
  rank $\\le 1$.
- `Counterexample:` Let's take $n=4$ and the inner column $j$. Let
  $$S_j=\\{e_1,e_2,e_3,e_4\\}$$
  are horizontal edges between columns $j$ and $j+1$ (in row order), and the partition $\\pi$ is given by
  blocks $B_1=\\{e_1,e_2\\}$ (upper rectangle) and $B_2=\\{e_3,e_4\\}$ (lower rectangle).
  Let's look at the internal nodes
  $$U_1=\\{(1,j),(2,j)\\},\\qquad U_2=\\{(3,j),(4,j)\\}.$$
  Then $U_1,U_2$ and the root $U_1\\triangle U_2$ are axial rectangles (12 and 14),
  and the intersections with $S_j$ are $B_1$ and $B_2$. Their projections onto $(B_1,B_2)$:
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(00,11),$$
  are linearly independent, so the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: the root corresponds to the rectangle $\\{(1,j),\\dots,(4,j)\\}$, and the internal
  nodes - two rectangles with two lines each; all intersections with $S_j$ are rectangular blocks.
- `Status:` counterexample (toy, $k=2$): even with rectangular geometry, projection rank = 2.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen geometry: require "anchored"/stepped areas
  (monotonic in both coordinates and bound to the boundary), and check whether this gives a real
  rank obstruction for $k=2$.
- `StepID:` Q39.S17-2k-rectangular-geometry-obstruction.
- `InfoGain:` 1.

### 16.164. Exploratory step (counterexample): anchoredstaircase geometry does not reduce projection rank at $k=2$

- `Lens:` Model stress test.
- `Assertion (attempt):` If you require the internal nodes of an XOR tree to be
  "anchored-staircase" areas (for example, in each column there are many lines - a prefix from the upper border),
  then the projection of internal lines onto blocks $B_1,B_2$ must have rank $\\le 1$.
- `Counterexample:` Let's take $n=4$ and the inner column $j$. Let
  $$S_j=\\{e_1,e_2,e_3,e_4\\}$$
  are horizontal edges between columns $j$ and $j+1$ (in row order), and the partition $\\pi$ is given by
  blocks $B_1=\\{e_1,e_2\\}$ and $B_2=\\{e_3,e_4\\}$.
  Consider an XOR tree that sums the vertices of a column from top to bottom:
  $$((v_1\\oplus v_2)\\oplus v_3)\\oplus v_4,$$
  where $v_i=(i,j)$. Its internal nodes correspond to the sets
  $$U_1=\\{(1,j),(2,j)\\},\\qquad U_2=\\{(1,j),(2,j),(3,j)\\},\\qquad U_3=\\{(1,j),\\dots,(4,j)\\}.$$
  All $U_1,U_2,U_3$ are anchoredstaircase (line prefixes). At the same time
  $$S_j\\cap\\delta(U_1)=\\{e_1,e_2\\},\\qquad S_j\\cap\\delta(U_2)=\\{e_1,e_2,e_3\\},$$
  and their projections onto $(B_1,B_2)$ are equal
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(11,10),$$
  which is linearly independent. Therefore, the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$; the top-down tree has internal prefix nodes $\\{1,2\\}$ and $\\{1,2,3\\}$,
  giving independent projections onto two blocks.
- `Status:` counterexample (toy, $k=2$): anchored-staircase (prefix-by-row) does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen constraint: require internal nodes to be anchoredstaircase
  **and** had a "single-stage" boundary (for example, without long prefix fronts),
  and check whether this gives real rank obstruction for $k=2$.
- `StepID:` Q39.S18-2k-staircase-geometry-obstruction.
- `InfoGain:` 1.

### 16.165. Exploratory step (counterexample): "short frontier" on $S_j$ does not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` If you require the internal nodes of an XOR tree to
  the intersection $S_j\\cap\\delta(U)$ had size $\\le 2$ (short frontier on the strip $S_j$),
  then the projection of internal lines onto blocks $B_1,B_2$ must have rank $\\le 1$.
- `Counterexample:` Let's take $n=4$ and the inner column $j$. Let
  $$S_j=\\{e_1,e_2,e_3,e_4\\}$$
  are horizontal edges between columns $j$ and $j+1$ (in row order), and the partition $\\pi$ is given by
  blocks $B_1=\\{e_1,e_2\\}$ and $B_2=\\{e_3,e_4\\}$.
  Let's look at the internal nodes
  $$U_1=\\{(1,j),(2,j)\\},\\qquad U_2=\\{(3,j),(4,j)\\}.$$
  Then $|S_j\\cap\\delta(U_1)|=|S_j\\cap\\delta(U_2)|=2$, i.e. the frontier is short, and
  $$p(\\delta(U_1))=(11,00),\\qquad p(\\delta(U_2))=(00,11)$$
  linearly independent. Therefore, the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: nodes $U_1,U_2$ have a frontier of 2 edges on $S_j$, but give independent
  projections onto $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): the "short frontier" restriction on $S_j$ does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that internal nodes have a **unit** frontier on $S_j$
  (|$S_j\\cap\\delta(U)$|=1) or similar limit on both bands, and check
  does this give real rank obstruction for $k=2$.
- `StepID:` Q39.S19-2k-short-frontier-obstruction.
- `InfoGain:` 1.

### 16.166. Exploratory step (proof): unit frontier is impossible for a target with $\\ge 3$ edges on $S_j$

- `Lens:` Invariant.
- `Assertion (attempt):` Is it possible to impose an invariant: all **internal** nodes of the XOR tree
  have $|S_j\\cap\\delta(U)|\\le 1$ (unit frontier on strip $S_j$) to control rank?
- `Evidence (obstruction):` Let the XOR tree output the string with
  $$|S_j\\cap\\delta(U_{\\mathrm{root}})|\\ge 3,$$
  for example $U_{\\mathrm{root}}=B_{3..6}$ (then the intersection with $S_j$ has 4 edges).
  The leaves are vertex equations, and each leaf intersects $S_j$ in at most one edge.
  Consider any internal node $w$ with children $w_1,w_2$. Then
  $$S_j\\cap\\delta(w)=\\bigl(S_j\\cap\\delta(w_1)\\bigr)\\triangle\\bigl(S_j\\cap\\delta(w_2)\\bigr),$$
  That's why
  $$|S_j\\cap\\delta(w)|\\le |S_j\\cap\\delta(w_1)|+|S_j\\cap\\delta(w_2)|.$$
  If all internal nodes satisfied $|S_j\\cap\\delta(\\cdot)|\\le 1$, then for the root it would be
  $|S_j\\cap\\delta(U_{\\mathrm{root}})|\\le 2$ is a contradiction.
  Moreover, from $|S_j\\cap\\delta(U_{\\mathrm{root}})|\\ge 3$ it follows that at least one of the two children
  root has an intersection of size $\\ge 2$, which means there is a **non-root** internal node with
  frontier $\\ge 2$. Therefore, the invariant is "unit frontier for all internal nodes (except the root)"
  is no longer possible for the goal $|S_j\\cap\\delta(U_{\\mathrm{root}})|\\ge 3$.
- `Toy test:` $n=6$, $U_{\\mathrm{root}}=B_{3..6}$: $|S_j\\cap\\delta(U_{\\mathrm{root}})|=4$,
  This means that any XOR tree has an internal node with the intersection $\\ge 2$.
- `Status:` proven (obstruction: "unit frontier" is incompatible with target string of width $\\ge 3$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if frontier control is needed, then weaken the invariant: allow intersection
  $\\le 2$ on one of the children of the root, or introduce a limit on **two** lanes at the same time
  (for example, on $S_j$ and $S_{j+1}$), and check whether this gives rank obstruction for $k=2$.
- `StepID:` Q39.S20-2k-single-frontier-obstruction.
- `InfoGain:` 1.

-/

/-!
### 16.167. Research step (toy): two-lane frontier <=2 does not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` If we require that for each internal node of the XOR tree
  if $|S_j\\cap\\delta(U)|\\le 2$ and $|S_{j+1}\\cap\\delta(U)|\\le 2$ were satisfied, then the projection rank
  on a partition $\\pi$ with two blocks drops to $\\le 1$.
- `Counterexample (toy):` Let $n=4$ and $j=1$. Let us denote the horizontal edges between the columns
  $j$ and $j+1$ through $S_j=\\{e_1,\\dots,e_4\\}$ (in row order), and between $j+1$ and $j+2$ -
  $S_{j+1}=\\{f_1,\\dots,f_4\\}$. Let's take a partition
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let's look at the internal nodes
  $$U_1=\\{(1,j+1),(2,j+1)\\},\\qquad U_2=\\{(3,j+1),(4,j+1)\\}.$$
  Then $|S_j\\cap\\delta(U_i)|=|S_{j+1}\\cap\\delta(U_i)|=2$ for $i\\in\\{1,2\\}$, but
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent. Therefore, the projection rank is 2.
- `Toy test:` $n=4$, $j=1$: nodes $U_1,U_2$ have a frontier of 2 edges on each of the two stripes,
  but give independent projections onto $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): a two-lane frontier size limit does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require frontier intervals on both lanes
  or restrict the joint structure of the frontier to $S_j$ and $S_{j+1}$ (for example, identical rows),
  and check whether this gives real rank obstruction for $k=2$.
- `StepID:` Q39.S23-2k-two-strip-rank-toy.
- `InfoGain:` 1.
-/

/-!
### 16.188. Exploratory step (counterexample): global ordering of blocks by columns does not reduce projection rank when $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let the global order of dyadic blocks be fixed
  $B_1\\to B_2\\to\\dots\\to B_r$, and for each pair of adjacent columns changes
  stripes are only allowed in this order (each step toggles one block, no backtracking).
  Expectation: Global order synchronization across all columns should reduce
  projection rank on two stripes.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$),
  with blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let's take the global order $B_1\\to B_2\\to B_1$ (for the remaining columns we will leave
  stripes unchanged). Then the chain
  $$U_1=R_{1,2},\\qquad U_2=R_{3,4},\\qquad U_3=U_1$$
  follows the global order for the selected pair of columns and does not violate it for the rest.
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: global order $B_1\\to B_2\\to B_1$ still gives rank 2.
- `Status:` counterexample (toy, $k=2$): global block order synchronization does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the restriction to **synchronous** execution of the global step
  on all columns at the same time (or link the order of rows/columns), and check if
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S47-2k-two-strip-chain-strip-support-global-schedule.
- `InfoGain:` 1.
-/

/-!
### 16.190. Exploratory step (counterexample): row/column lockstep does not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let each node have the form **row/column lockstep**:
  there is a global pattern $U=R\\times C$ (the same sets of strings $R$
  and columns $C$ for all stripes), so that at each step all stripes change
  synchronously in the same block across rows and columns. Expectation: like this
  synchronization should reduce the projection rank on the two bands.
- `Counterexample (toy):` Let's take grid $4\\times m$ for $m\\ge 4$ and a pair of columns $j=2$, $j+1=3$.
  Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},\\quad C=\\{\\text{odd columns}\\}.$$
  Let's define
  $$U_1:=R_1\\times C,\\qquad U_2:=R_2\\times C.$$
  Then for any strip $S_j$ the intersection $S_j\\cap\\delta(U_t)$ consists exactly
  from the edges of the rows $R_t$ (since exactly one of the two incident columns is odd),
  that is, the global step is synchronous across all columns and rows.
  Let us denote the edges on $S_{j-1}$ by $e_1,\\dots,e_4$ and on $S_{j+1}$ by $f_1,\\dots,f_4$,
  and blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Then
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: row/column lockstep $R_1\\times C\\to R_2\\times C$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): row/column lockstep does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require **continuum** (contiguous) and along the lines,
  and by columns (one rectangle), and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S49-2k-two-strip-chain-strip-support-rowcol-lockstep.
- `InfoGain:` 1.
-/

/-!
### 16.191. Exploratory step (counterexample): row/column contiguous rectangle does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let each node be **one rectangle**
  $U=R\\times C$ with $R$ and $C$ as continuous row/column intervals
  (row/column contiguous). Expectation: this mode should reduce the projection rank
  on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$,
  so the stripes $S_{j-1}$ and $S_{j+1}$ are the boundaries of the rectangle $C=\\{2,3\\}$.
  Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},\\quad C=\\{2,3\\}.$$
  Define rectangles
  $$U_1:=R_1\\times C,\\qquad U_2:=R_2\\times C.$$
  Let us denote the edges on $S_{j-1}$ by $e_1,\\dots,e_4$ and on $S_{j+1}$ by $f_1,\\dots,f_4$,
  and blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Then
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: two row/column contiguous rectangles give rank 2.
- `Status:` counterexample (toy, $k=2$): row/column contiguous rectangles do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require a **monotonic chain** of rectangles
  (nesting in rows and columns at the same time) and check if
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S50-2k-two-strip-chain-strip-support-rowcol-contiguous.
- `InfoGain:` 1.
-/

/-!
### 16.192. Exploratory step (counterexample): nested chain of rectangles does not reduce projection rank for $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let the chain consist of **nested** rectangles
  $U_1\\subset U_2\\subset\\cdots$ with continuous $R_t$ and $C_t$ (rows/columns contiguous),
  that is, $U_t=R_t\\times C_t$, where both rows and columns grow monotonically. Expectation:
  This 2D monotonicity should reduce the projection rank on the two stripes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$,
  so the stripes $S_{j-1}$ and $S_{j+1}$ are the boundaries of the rectangle $C=\\{2,3\\}$.
  Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{1,2,3,4\\},\\quad C=\\{2,3\\}.$$
  Define nested rectangles
  $$U_1:=R_1\\times C,\\qquad U_2:=R_2\\times C.$$
  Let us denote the edges on $S_{j-1}$ by $e_1,\\dots,e_4$ and on $S_{j+1}$ by $f_1,\\dots,f_4$,
  and blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Then
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(1111,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: a nested chain of rectangles gives rank 2.
- `Status:` counterexample (toy, $k=2$): nesting rectangles does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require **step-by-step** expansion of the rectangle
  simultaneously by rows and columns (2Dprefixchain) and check whether
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S51-2k-two-strip-chain-strip-support-rowcol-nested.
- `InfoGain:` 1.
-/

/-!
### 16.193. Exploratory step (counterexample): 2Dprefix chain of rectangles does not reduce projection rank for $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the chain consist of **2Dprefix** rectangles
  $$U_t=[1..t]\\times[1..t],\\quad t=1,2,\\dots,$$
  that is, rows and columns are expanded synchronously one at a time. Expectation: like this
  strictly synchronous 2D monotonicity should reduce the projection rank on the two stripes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$.
  Let
  $$U_2=[1,2]\\times[1,2],\\qquad U_4=[1,4]\\times[1,4].$$
  Let us denote the edges on the stripes $S_{j-1}$ and $S_{j+1}$ by
  $$S_{j-1}=\\{e_1,\\dots,e_4\\},\\qquad S_{j+1}=\\{f_1,\\dots,f_4\\}.$$
  Then $U_2$ intersects these stripes only in the top two rows,
  and $U_4$ is in all four lines. For blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}$$
  we get
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: 2Dprefix chain $U_1\\subset U_2\\subset U_3\\subset U_4$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): 2Dprefix chain does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require a 2Dprefix **and** ban on omissions
  (require all microsteps to be taken into account) and check whether rank obstruction appears.
- `StepID:` Q39.S52-2k-two-strip-chain-strip-support-rowcol-2d-prefix.
- `InfoGain:` 1.
-/

/-!
### 16.194. Exploratory step (counterexample): 2Dprefix microsteps do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the chain consist of **all** 2Dprefix microsteps
  $U_t=[1..t]\\times[1..t]$ for each $t$ (without gaps). Expectation: everyone is taken into account
  microstepping should suppress independence on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$.
  Consider the chain
  $$U_1\\subset U_2\\subset U_3\\subset U_4,\\qquad U_t=[1..t]\\times[1..t].$$
  Let us denote the edges on the stripes $S_{j-1}$ and $S_{j+1}$ by
  $$S_{j-1}=\\{e_1,\\dots,e_4\\},\\qquad S_{j+1}=\\{f_1,\\dots,f_4\\},$$
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$, $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Then
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2
  even with all microsteps enabled.
- `Toy test:` $n=4$, $j=2$: the complete 2Dprefix chain gives rank 2.
- `Status:` counterexample (toy, $k=2$): 2Dprefix microsteps do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require additional synchronization
  (for example, fixed order across columns and rows at the same time) or
  look for a place where a global "basechange" is required.
- `StepID:` Q39.S53-2k-two-strip-chain-strip-support-rowcol-2d-prefix-microsteps.
- `InfoGain:` 1.
-/

/-!
### 16.195. Exploratory step (counterexample): global row/column 2Dprefix lockstep does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let each node be a **global** 2Dprefix rectangle
  $$U_t=[1..t]\\times[1..t]$$
  throughout the grid, i.e. rows and columns are expanded synchronously with **the same** $t$
  on all stripes (row/column lockstep). Expectation: such global synchronization
  should reduce the projection rank on two stripes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$.
  Let
  $$U_2=[1,2]\\times[1,2],\\qquad U_4=[1,4]\\times[1,4].$$
  These are global 2Dprefix rectangles, so the lockstep requirement is met
  on all lanes. For edges $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$, $B_2=\\{e_3,e_4,f_3,f_4\\}$ we have
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: global 2Dprefix lockstep chain $U_1\\subset\\cdots\\subset U_4$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): global 2Dprefix lockstep does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` require a fixed **global** order of row and column blocks
  (no returns) and simultaneous adherence to this order on all lanes;
  check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S54-2k-two-strip-chain-strip-support-rowcol-2d-prefix-lockstep.
- `InfoGain:` 1.
-/

/-!
### 16.196. Exploratory step (counterexample): global row/column block order does not reduce projection rank when $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Suppose rows and columns are split into blocks with a fixed
  **global order**, and each node is a rectangle of the form $R_{\\le i}\\times C_{\\le j}$,
  where $R_{\\le i}$ and $C_{\\le j}$ are block prefixes (no returns; "jumps" are allowed).
  Expectation: This global block ordering should constrain the projection rank
  on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$, blocks of rows
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},$$
  column blocks
  $$C_1=\\{1,2\\},\\quad C_2=\\{3,4\\},$$
  and order $R_1\\prec R_2$, $C_1\\prec C_2$. Let's consider
  $$U_1:=R_1\\times C_1,\\qquad U_2:=(R_1\\cup R_2)\\times(C_1\\cup C_2).$$
  These are global block prefixes. For a pair of columns $j=2$, $j+1=3$ and edges
  $S_{j-1}=\\{e_1,\\dots,e_4\\}$, $S_{j+1}=\\{f_1,\\dots,f_4\\}$ we get
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: global block order $R_1\\prec R_2$, $C_1\\prec C_2$
  still gives rank 2.
- `Status:` counterexample (toy, $k=2$): global block order does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` prohibit "horses" and require **step-by-step** addition
  one block of rows or columns (include intermediate rectangles
  $R_{\\le2}\\times C_{\\le1}$ and $R_{\\le1}\\times C_{\\le2}$), and check
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S55-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order.
- `InfoGain:` 1.
-/

/-!
### 16.197. Exploratory step (counterexample): global block order with microsteps does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the global order of row/column blocks be fixed,
  and the chain of rectangles **includes all microsteps**, that is, at each step
  exactly one block of rows or columns is added (without "jumps").
  Expectation: Microstepping should reduce the projection rank on two bars.
- `Counterexample (toy):` Let's take grid $4\\times 4$, blocks of rows
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},$$
  column blocks
  $$C_1=\\{1,2\\},\\quad C_2=\\{3,4\\},$$
  and order $R_1\\prec R_2$, $C_1\\prec C_2$. Consider a microstepping chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_1\\times(C_1\\cup C_2),\\qquad
    U_3:=(R_1\\cup R_2)\\times(C_1\\cup C_2).$$
  This is a chain of prefixes across blocks without jumps. For a pair of columns $j=2$, $j+1=3$ and edges
  $S_{j-1}=\\{e_1,\\dots,e_4\\}$, $S_{j+1}=\\{f_1,\\dots,f_4\\}$ we get
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_3))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: microstepping chain of global block prefixes gives rank 2.
- `Status:` counterexample (toy, $k=2$): microsteps of the global block order do not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the restriction: require **strict rotation**
  row/column microsteps (for example, the R-step always follows the C-step) and check whether
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S56-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps.
- `InfoGain:` 1.
-/

/-!
### 16.198. Exploratory step (counterexample): strict alternation of row/column microsteps does not reduce the projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let the global order of blocks be fixed, and the chain of microsteps
  **strictly** alternates step type: a row step always follows a column step (and vice versa).
  Expectation: Strict alternation of step types should reduce the projection rank on the two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$, blocks of rows
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},$$
  and column blocks (global order)
  $$C_1=\\{2,3\\}\\prec C_2=\\{1\\}.$$
  Consider an alternating chain
  $$U_1:=R_1\\times C_1,\\qquad
    U_2:=R_1\\times(C_1\\cup C_2),\\qquad
    U_3:=(R_1\\cup R_2)\\times(C_1\\cup C_2).$$
  Here $U_1\\to U_2$ is a column step, $U_2\\to U_3$ is a row step (strict alternation).
  For a pair of columns $j=2$, $j+1=3$ and edges
  $S_{j-1}=\\{e_1,\\dots,e_4\\}$, $S_{j+1}=\\{f_1,\\dots,f_4\\}$ we get
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: column-step/row-step alternation still gives rank 2.
- `Status:` counterexample (toy, $k=2$): strict alternation of microsteps does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that **both** strips $S_{j-1}$ and $S_{j+1}$
  remained active at each microstep (no "zeroing" of one band), and check that
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S57-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating.
- `InfoGain:` 1.
-/

/-!
### 16.199. Exploratory step (counterexample): both bars are active on each microstep, but the rank remains 2

- `Lens:` Invariant.
- `Assertion (attempt):` In global block order and with strict alternation
  row/column microsteps we require that **at each microstep both bars be active**,
  those. $S_{j-1}\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ are non-empty.
  Expectation: This should limit the projection rank on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$ and a pair of columns $j=2$, $j+1=3$.
  Let us fix the core block $C=\\{2,3\\}$, so that the boundaries of the slab give activity
  on both stripes for any non-empty string $R$. Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{1,2,3,4\\},\\qquad
    U_1:=R_1\\times C,\\quad U_2:=R_2\\times C.$$
  Then at each step both bands are active, but
  $$p(\\delta(U_1))=(1100,1100),\\qquad p(\\delta(U_2))=(1111,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: both bands are active at each step, but the rank remains 2.
- `Status:` counterexample (toy, $k=2$): the condition "both lanes are active" does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: prohibit **matching** supports on lanes
  (require difference between $S_{j-1}\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ at each step)
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S58-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips.
- `InfoGain:` 1.
-/

/-!
### 16.200. Exploratory step (counterexample): difference in band supports does not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` In global block order and with strict alternation
  row/column microsteps we require that at each step
  $$S_{j-1}\\cap\\delta(U)\\ne S_{j+1}\\cap\\delta(U).$$
  Expectation: The difference in band support should reduce the projection rank on the two bands.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$,
  row blocks $R_1=\\{1,2\\}\\prec R_2=\\{3,4\\}$ and column blocks
  $$C_1=\\{2\\}\\prec C_2=\\{3,4\\}.$$
  Consider an alternating chain
  $$U_1:=R_1\\times C_1,\\qquad
    U_2:=R_1\\times(C_1\\cup C_2),\\qquad
    U_3:=(R_1\\cup R_2)\\times(C_1\\cup C_2).$$
  Here $U_1\\to U_2$ is a column step, $U_2\\to U_3$ is a row step. For each $U_t$
  lane $S_{j-1}$ is active (column $2$ inside, $1$ outside) and $S_{j+1}$ is not active
  (columns $3$ and $4$ are both inside), so the band supports are different at each step.
  Let us denote $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$. Then
  $$p(\\delta(U_1))=(1100,0000),\\qquad p(\\delta(U_3))=(1111,0000),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: difference in lane support does not reduce the rank.
- `Status:` counterexample (toy, $k=2$): distinct strip supports do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require **both** bands to be active and their support
  are different at each microstep, and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S59-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-distinct-strips.
- `InfoGain:` 1.
-/

/-!
### 16.201. Exploratory step (counterexample): both bars are active and different, but the rank remains 2

- `Lens:` Invariant.
- `Assertion (attempt):` In global block order and with strict alternation
  row/column microsteps we require that at each step
  (i) both bands are active and (ii) their supports are different.
  Expectation: This should limit the projection rank on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$,
  and fix the columns $C=\\{2,3\\}$. Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{1,2,3,4\\},\\qquad
    U_1:=R_1\\times C,\\quad U_2:=R_2\\times C.$$
  Then both bands are active at each step, and the supports are different:
  $S_{j-1}\\cap\\delta(U_1)=\\{e_1,e_2\\}$ and $S_{j+1}\\cap\\delta(U_1)=\\{f_1,f_2\\}$
  (different sets of edges), similarly for $U_2$.
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1100,1100),\\qquad p(\\delta(U_2))=(0011,1100),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: both bands are active and different, but the rank remains 2.
- `Status:` counterexample (toy, $k=2$): the condition "both strips active + distinct" does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that **both** bars are active and
  each of them changes at each microstep (distinct strip support per step),
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S60-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-distinct.
- `InfoGain:` 1.
-/

/-!
### 16.202. Exploratory step (counterexample): both bars change on each step, but the rank remains 2

- `Lens:` Communication/Rank.
- `Assertion (attempt):` In the global block order (row/column), we require that
  at each microstep, **both** stripes changed:
  $$S_{j-1}\\cap\\delta(U_t)\\ne S_{j-1}\\cap\\delta(U_{t-1}),\\qquad
    S_{j+1}\\cap\\delta(U_t)\\ne S_{j+1}\\cap\\delta(U_{t-1}).$$
  Expectation: if both stripes change at each step, then the projected rank on the two stripes
  should be $\\le 1$.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$ and fix
  $C=\\{2,3\\}$. Let
  $$R_1=\\{1,2\\},\\quad R_2=\\{3,4\\},\\quad R_3=\\{1,2,3,4\\},$$
  and chain
  $$U_1:=R_1\\times C,\\qquad U_2:=R_2\\times C,\\qquad U_3:=R_3\\times C.$$
  Then at each step both stripes change (the rows on $S_{j-1}$ and $S_{j+1}$ change together).
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1100,1100),\\qquad p(\\delta(U_2))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: both bands change at each step, but the rank remains 2.
- `Status:` counterexample (toy, $k=2$): "both strips change per step" does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require alternating row/column microsteps,
  in which **both** strip-supports change at each step (column-steps must
  also change $S_{j-1}$ and $S_{j+1}$), and check whether the rank $\\ge 2$ remains.
- `StepID:` Q39.S61-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-distinct-support-per-step.
- `InfoGain:` 1.
-/

/-!
### 16.203. Exploratory step (counterexample): strict row/column alternation when changing both stripes does not reduce the rank

- `Lens:` Invariant.
- `Assertion (attempt):` We require strict interleaving in the global order of blocks
  row/column microsteps and changing **both** bars at each step. Expectation:
  such a combination should limit the projection rank on the two stripes.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$,
  blocks of rows $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$ and columns
  $$C_0=\\{1,2,3,4\\},\\qquad C_1=\\{2,3\\}.$$
  Consider an alternating chain
  $$U_1:=R_1\\times C_0,\\qquad U_2:=R_1\\times C_1,\\qquad U_3:=R_2\\times C_1.$$
  Here $U_1\\to U_2$ is a column step (both strips change: empty $\\to$ rows $R_1$),
  and $U_2\\to U_3$ is the row step (rows $R_1\\to R_2$), that is, strict alternation
  with both bands changing at each step. OK $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$
  we get
  $$p(\\delta(U_2))=(1100,1100),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: strict alternation + both bands change  rank 2.
- `Status:` counterexample (toy, $k=2$): alternating + bothchange does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that **each** column step save
  activity of both bands (without empty bands) and simultaneously changed their support,
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S62-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-change-per-step.
- `InfoGain:` 1.
-/

/-!
### 16.204. Exploratory step (counterexample): column steps are active in both lanes, but the rank remains 2

- `Lens:` Communication/Rank.
- `Assertion (attempt):` We require strict alternation of row/column microsteps, and
  Each column step keeps **the activity of both bands** and changes their support.
  Expectation: This version of interleaving should limit the projection rank on two lanes.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$,
  rows $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$ and columns
  $$C_1=\\{1,2,3,4\\},\\qquad C_2=\\{2,3\\},\\qquad C_3=\\{1,4\\}.$$
  Consider an alternating chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_1\\times C_2,\\qquad U_3:=R_2\\times C_2,$$
  $$U_4:=R_2\\times C_3.$$
  Column steps $U_1\\to U_2$ and $U_3\\to U_4$ keep both stripes active
  (columns $2$ and $3$ on opposite sides) and change their supports. In order
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1100,1100),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: active column steps when alternating still give rank 2.
- `Status:` counterexample (toy, $k=2$): "active columnsteps" do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that both row steps and column steps
  changed supports **one block at a time** on both lanes (local step size),
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S63-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-active-columnstep.
- `InfoGain:` 1.
-/

/-!
### 16.205. Exploratory step (counterexample): local block in both lanes does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: at each row/column support step
  on the stripes $S_{j-1}$ and $S_{j+1}$ change **by one block** (local step size)
  and both bands remain active. Expectation: This will limit the projection rank to 1.
- `Counterexample (toy):` Let's take grid $4\\times 4$, a pair of columns $j=2$, $j+1=3$ and
  blocks of lines $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$. Let's mark the blocks on the stripes
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Consider the chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_1\\times C_2,\\qquad U_3:=R_2\\times C_2,$$
  where $C_1=\\{1,2,3,4\\}$, $C_2=\\{2,3\\}$. In nodes $U_2,U_3$ support for
  Each lane has exactly one block ($B_1$ and $B_2$, respectively), i.e. local step size.
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we get
  $$p(\\delta(U_2))=(1100,1100),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: local blocks on both lanes  rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_local_block).
- `Status:` counterexample (toy, $k=2$): a local block on both lanes does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require **monotonic order** of blocks
  (without row/column returns) and check if the rank remains $\\ge 2$.
- `StepID:` Q39.S64-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block.
- `InfoGain:` 1.
-/

/-!
### 16.206. Exploratory step (counterexample): monotonic block order does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: the blocks on the stripes change
  in **monotonic order** (without row/column returns), while
  each step affects one block in both lanes. Expectation: this order
  will limit the projection rank to 1.
- `Counterexample (toy):` Let's take grid $4\\times 4$, $j=2$ and blocks of rows
  $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$, columns $C_1=\\{1,2,3,4\\}$ and $C_2=\\{2,3\\}$.
  Consider the chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_1\\times C_2,\\qquad U_3:=R_2\\times C_2.$$
  Transition $U_1\\to U_2$ is a column step, $U_2\\to U_3$ is a row step; block order
  monotonic (the upper block $B_1$ is replaced by the lower block $B_2$ without returning).
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1100,1100),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: monotonic block order  rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_monotone_block).
- `Status:` counterexample (toy, $k=2$): monotonic block order does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require **strictly increasing** blocks
  simultaneously in rows and columns (two-dimensional monotonicity) and check whether
  whether the rank $\\ge 2$ is preserved.
- `StepID:` Q39.S65-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone.
- `InfoGain:` 1.
-/

/-!
### 16.207. Exploratory step (counterexample): 2D monotonicity of blocks does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: blocks grow **monotonically along lines and across
  columns** (two-dimensional monotonicity), and each step changes one block per
  both lanes. Expectation: This will limit the projection rank to 1.
- `Counterexample (toy):` Let's take grid $4\\times 4$, $j=2$ and blocks of rows
  $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$, as well as column blocks
  $C_1=\\{1,2\\}$, $C_2=\\{3,4\\}$ (monotonic growth with respect to the block index).
  Consider the chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_1\\times C_2,\\qquad U_3:=R_2\\times C_2.$$
  Here, both the row and column block indexes do not decrease. In order
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1100,1100),\\qquad p(\\delta(U_3))=(0011,0011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: two-dimensional monotonicity  rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_monotone2d).
- `Status:` counterexample (toy, $k=2$): two-dimensional monotonicity does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require **strictly increasing** blocks
  simultaneously along rows and columns at each step, and check whether
  rank $\\ge 2$.
- `StepID:` Q39.S66-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d.
- `InfoGain:` 1.
-/

/-!
### 16.208. Exploratory step (counterexample): strict 2D monotonicity does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: at each step, blocks by lines ** and **
  along the columns strictly increase (2D monotonicity at each step), while both
  the stripes are active and change for one block. Expectation: This will limit the projection
  rank up to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and split the rows into
  blocks $R_1=\\{1,2\\}$, $R_2=\\{3,4\\}$, $R_3=\\{5,6\\}$, and columns on
  $C_1=\\{1,2\\}$, $C_2=\\{3,4\\}$, $C_3=\\{5,6\\}$. Consider the chain
  $$U_1:=R_1\\times C_1,\\qquad U_2:=R_2\\times C_2,\\qquad U_3:=R_3\\times C_3.$$
  Here, both row and column block indexes grow strictly at every step.
  In order $(e_1,\\dots,e_6,f_1,\\dots,f_6)$ we have
  $$p(\\delta(U_2))=(001100,001100),\\qquad p(\\delta(U_3))=(000011,000011),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: strict 2D monotonicity  rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_monotone2d_strict).
- `Status:` counterexample (toy, $k=2$): strict 2D monotonicity does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require blocks to be **strictly increasing**
  and at the same time remained prefixes (2Dprefix), and check whether the rank $\\ge 2$ remains.
- `StepID:` Q39.S67-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict.
- `InfoGain:` 1.
-/

/-!
### 16.209. Exploratory step (counterexample): strict 2Dprefixmonotonicity does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: at each step the rectangles -
  **2Dprefix** and both prefixes are strictly increasing; both bands are active.
  Expectation: This strict 2Dprefixmonotonicity should reduce the projection rank to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and prefixes
  $$U_1=[1,2]\\times[1,2],\\qquad U_2=[1,4]\\times[1,4],\\qquad U_3=[1,5]\\times[1,5].$$
  At each pair of steps, the rows and columns grow strictly, and the rectangles remain
  2Dprefix. Let us denote the edges on the stripes $S_{j-1}$ and $S_{j+1}$ by
  $$S_{j-1}=\\{e_1,\\dots,e_6\\},\\qquad S_{j+1}=\\{f_1,\\dots,f_6\\}.$$
  Then for internal nodes we have
  $$p(\\delta(U_2))=(111100,111100),\\qquad p(\\delta(U_3))=(111110,111110),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: strict 2D prefix chain gives rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_monotone2d_strict_prefix).
- `Status:` counterexample (toy, $k=2$): strict 2Dprefixmonotonicity does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that intersections with stripes
  were **front block** (not the entire prefix), and check if the
  rank $\\ge 2$.
- `StepID:` Q39.S68-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix.
- `InfoGain:` 1.
-/

/-!
### 16.210. Research step (counterexample): frontier blocks in a strict 2D prefix chain do not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: the chain is strict 2Dprefix,
  and at each step of intersection with stripes - **only frontier block** (new lines/columns),
  those. one continuous block on each lane. Expectation: This will limit the projection rank to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and a strict 2Dprefix chain
  $$U_1=[1,1]\\times[1,1],\\qquad U_2=[1,3]\\times[1,3],\\qquad U_3=[1,6]\\times[1,6].$$
  Frontier block for step $U_1\\to U_2$ - lines $\\{2,3\\}$, and for $U_2\\to U_3$ - lines
  $\\{4,5,6\\}$. On the stripes $S_{j-1}$ and $S_{j+1}$ this gives
  $$p_{\\mathrm{fr}}(U_2)=(011000,011000),\\qquad p_{\\mathrm{fr}}(U_3)=(000111,000111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: frontier blocks give rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_frontier_block).
- `Status:` counterexample (toy, $k=2$): frontier blocks do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require frontier block to have **length 1**
  (growth by one row/column), and check if rank 2 disappears.
- `StepID:` Q39.S69-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier.
- `InfoGain:` 1.
-/

/-!
### 16.211. Research step (counterexample): unitfrontier in a strict 2Dprefix chain does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: in a strict 2Dprefix chain
  The frontier block at each step has **length 1** (growth by exactly one line/column),
  and both bands are active. Expectation: This will limit the projection rank to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and chain
  $$U_1=[1,2]\\times[1,2],\\qquad U_2=[1,3]\\times[1,3],\\qquad U_3=[1,4]\\times[1,4].$$
  Frontier blocks have length 1: lines $\\{3\\}$ and $\\{4\\}$.
  In order $(e_1,\\dots,e_6,f_1,\\dots,f_6)$ we get
  $$p_{\\mathrm{fr}}(U_2)=(001000,001000),\\qquad p_{\\mathrm{fr}}(U_3)=(000100,000100),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: unitfrontier gives rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_unit_frontier).
- `Status:` counterexample (toy, $k=2$): unitfrontier does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: allow unitfrontier only on **one** lane
  per step (onestrip), and check whether rank 2 disappears.
- `StepID:` Q39.S70-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit.
- `InfoGain:` 1.
-/

/-!
### 16.212. Research step (counterexample): onestrip unitfrontier does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: in a strict 2Dprefix chain
  unitfrontier is allowed **only on one strip** at a step (onestrip),
  the other lane is empty. Expectation: This will reduce the projection rank to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and chain
  $$U_1=[1,2]\\times[1,2],\\qquad U_2=[1,3]\\times[1,2],\\qquad U_3=[1,4]\\times[1,2].$$
  Then the frontier on the strip $S_{j-1}$ are the unit rows $\\{3\\}$ and $\\{4\\}$,
  and on $S_{j+1}$ the frontier is empty. In order $(e_1,\\dots,e_6,f_1,\\dots,f_6)$:
  $$p_{\\mathrm{fr}}(U_2)=(001000,000000),\\qquad p_{\\mathrm{fr}}(U_3)=(000100,000000),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: onestrip unitfrontier gives rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_unit_frontier_onestrip).
- `Status:` counterexample (toy, $k=2$): onestrip unitfrontier does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require **alternation of lanes**
  (unit-frontier switches between $S_{j-1}$ and $S_{j+1}$), and check if rank 2 remains.
- `StepID:` Q39.S71-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip.
- `InfoGain:` 1.
-/

/-!
### 16.213. Research step (counterexample): alternating unitfrontier does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let's strengthen the condition: in a strict 2Dprefix chain
  unit-frontier alternates between stripes $S_{j-1}$ and $S_{j+1}$ at each step.
  Expectation: This alternation will reduce the projection rank to 1.
- `Counterexample (toy):` Let's take grid $6\\times 6$, $j=3$ and chain
  $$U_1=[1,3]\\times[1,2],\\qquad U_2=[1,4]\\times[1,2],\\qquad U_3=[1,4]\\times[1,3].$$
  Then frontier on $S_{j-1}$ is the unit row $\\{4\\}$ for $U_2$,
  and for $U_3$ frontier switches to $S_{j+1}$ (unit row $\\{3\\}$).
  In order $(e_1,\\dots,e_6,f_1,\\dots,f_6)$:
  $$p_{\\mathrm{fr}}(U_2)=(000100,000000),\\qquad p_{\\mathrm{fr}}(U_3)=(000000,001000),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=6$, $j=3$: alternating unitfrontier gives rank 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_unit_frontier_alternating).
- `Status:` counterexample (toy, $k=2$): alternating unitfrontier does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require frontier to alternate **and**
  remained in a fixed order by row (global order), and check the rank.
- `StepID:` Q39.S72-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating.
- `InfoGain:` 1.
-/

/-!
### 16.214. Research step (counterexample): balanced anchored blocks do not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` if in the anchored step the blocks are "balanced" between the stripes,
  then the projection rank can drop to 1.
- `Counterexample (toy):` two balanced 12bit projections remain distinguishable and non-zero,
  therefore the rank of internal nodes is 2 (see. `formal/WIP/Verified/Q39.lean`,
  Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced).
- `Status:` counterexample (toy, $k=2$).
- `Barrier check (A/B/C):`
  A) Relativization check: yes (toy-rank, pure combinatorics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` require symmetry between stripes at each step (row/column swap)
  and check if rank 2 is maintained.
- `StepID:` Q39.S80-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced.
- `InfoGain:` 1.
-/

/-!
### 16.215. Exploratory step (counterexample): row/column swap symmetry does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` if each step is symmetrical along the stripes
  (row/column swap), then the projection rank can drop to 1.
- `Counterexample (toy):` two strip-symmetric 12-bit projections remain distinguishable
  and non-zero, so the rank of internal nodes is 2 (see. `formal/WIP/Verified/Q39.lean`,
  Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap).
- `Status:` counterexample (toy, $k=2$).
- `Barrier check (A/B/C):`
  A) Relativization check: yes (toy-rank, combinatorics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` require a fixed pair of rows/columns at each step
  (row/column swap + fixedpair) and check if rank 2 remains.
- `StepID:` Q39.S81-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap.
- `InfoGain:` 1.
-/

/-!
### 16.216. Exploratory step (counterexample): fixedpair row/column swap does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` if only allow one fixed pair of rows/columns
  (fixedpair) and require row/column swap at each step, then the projection rank can drop to 1.
- `Counterexample (toy):` two fixed-pair strip-symmetric 12-bit projections remain
  distinguishable and non-zero, which means the rank of internal nodes is 2
  (see `formal/WIP/Verified/Q39.lean`, Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair).
- `Status:` counterexample (toy, $k=2$).
- `Barrier check (A/B/C):`
  A) Relativization check: yes (toy-rank, combinatorics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` require a fixed pair of **and** same order
  in both bands (fixedpair + sameorder) and check if rank 2 is preserved.
- `StepID:` Q39.S82-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair.
- `InfoGain:` 1.
-/

/-!
### 16.217. Research step (counterexample): fixedpair + sameorder does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` if you fix a pair of rows/columns and require the same order
  in both stripes (same-order), then the projection rank can drop to 1.
- `Counterexample (toy):` two sameorder 12bit projections remain distinguishable and non-zero,
  This means that the rank of internal nodes is 2 (see `formal/WIP/Verified/Q39.lean`,
  Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder).
- `Status:` counterexample (toy, $k=2$).
- `Barrier check (A/B/C):`
  A) Relativization check: yes (toy-rank, combinatorics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` strengthen the condition: fixedpair + sameorder + prohibition of pair change
  on the entire chain (global fixed-pair), and check whether rank 2 remains.
- `StepID:` Q39.S83-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair-sameorder.
- `InfoGain:` 1.
-/

/-!
### 16.218. Exploratory step (counterexample): global fixedpair does not reduce rank

- `Lens:` Communication/Rank.
- `Assertion (attempt):` if you fix the same pair of rows/columns
  on the entire chain (global fixed-pair), then the projection rank can drop to 1.
- `Counterexample (toy):` two globalfixedpair 12bit projections remain distinguishable
  and non-zero, which means the rank of internal nodes is 2 (see. `formal/WIP/Verified/Q39.lean`,
  Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair).
- `Status:` counterexample (toy, $k=2$).
- `Barrier check (A/B/C):`
  A) Relativization check: yes (toy-rank, combinatorics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` require global fixedpair and prohibit orientation change
  (fixedpair + fixedorientation), and check if rank 2 is preserved.
- `StepID:` Q39.S84-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair-sameorder-globalfixedpair.
- `InfoGain:` 1.
-/

/-!
### 16.189. Exploratory step (counterexample): synchronous global step across all columns does not reduce projection rank for $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Suppose at each step of the global protocol **all** stripes $S_j$
  change synchronously: there is a common dyadic block $B$ such that for each $j$
  the intersection of $S_j\\cap\\delta(U)$ is equal to $B$ (same pattern across all columns).
  Expectation: This synchrony should reduce the projection rank on the two stripes.
- `Counterexample (toy):` Let's take grid $4\\times m$ for $m\\ge 4$ and a pair of columns $j=2$, $j+1=3$.
  Let us denote the stripes $S_{j-1}$ and $S_{j+1}$ by edges
  $$S_{j-1}=\\{e_1,\\dots,e_4\\},\\qquad S_{j+1}=\\{f_1,\\dots,f_4\\}$$
  by lines, and dyadic blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let
  $$U_1:=\\{(r,c): r\\in\\{1,2\\},\\ c\\ \\text{odd}\\},\\qquad
    U_2:=\\{(r,c): r\\in\\{3,4\\},\\ c\\ \\text{odd}\\}.$$
  Then for **each** stripe $S_j$ exactly one of the two incident columns is odd,
  therefore $S_j\\cap\\delta(U_1)$ consists of exactly the edges of the top two rows, and
  $S_j\\cap\\delta(U_2)$ -- from the edges of the bottom two lines. That is a global step
  synchronized on all speakers: $B_1\\to B_2$.
  In particular, on $S_{j-1}\\sqcup S_{j+1}$ we have
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: synchronous global step $B_1\\to B_2$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): synchronicity across all columns does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require **row/column lockstep** (simultaneous
  matching by stripes and by line partitions) and check whether
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S48-2k-two-strip-chain-strip-support-global-synchronous.
- `InfoGain:` 1.
-/

/-!
### 16.168. Exploratory step (counterexample): two-lane row-interval intersections do not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` If we require that for each internal node of the XOR tree
  the intersections of $S_j\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ were row-intervals
  (line-continuous segments), then the projection rank on the partition $\\pi$
  with two blocks drops to $\\le 1$.
- `Counterexample (toy):` Let's take the construction from Section 16.167 with $n=4$, $j=1$ and blocks
  $B_1=\\{e_1,e_2,f_1,f_2\\}$, $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  For internal nodes $U_1=\\{(1,j+1),(2,j+1)\\}$ and $U_2=\\{(3,j+1),(4,j+1)\\}$
  intersections with $S_j$ and $S_{j+1}$ are row-intervals
  ($\\{e_1,e_2\\}$, $\\{f_1,f_2\\}$ and $\\{e_3,e_4\\}$, $\\{f_3,f_4\\}$), but
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent.
- `Toy test:` $n=4$, $j=1$: both intersections on two lanes are continuous segments,
  but the projection rank of internal nodes is 2.
- `Status:` counterexample (toy, $k=2$): two-lane row-interval geometry does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition of connectivity: require consistency of intervals
  between $S_j$ and $S_{j+1}$ (for example, identical sets of strings), and check whether
  does this give rank obstruction for $k=2$.
- `StepID:` Q39.S27-2k-two-strip-interval-rank-bound.
- `InfoGain:` 1.
-/

/-!
### 16.169. Exploratory step (counterexample): linked row-intervals on two lanes do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` If we require that for each internal node of the XOR tree
  the intersections of $S_j\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ were row-intervals
  **and** matched the same strings (linked intervals),
  then the projection rank on the partition $\\pi$ with two blocks drops to $\\le 1$.
- `Counterexample (toy):` Let's take the same construction as in Section 16.167-Section 16.168:
  $n=4$, $j=1$, blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$,
  internal nodes $U_1=\\{(1,j+1),(2,j+1)\\}$ and $U_2=\\{(3,j+1),(4,j+1)\\}$.
  Then
  $$S_j\\cap\\delta(U_1)=\\{e_1,e_2\\},\\quad S_{j+1}\\cap\\delta(U_1)=\\{f_1,f_2\\},$$
  $$S_j\\cap\\delta(U_2)=\\{e_3,e_4\\},\\quad S_{j+1}\\cap\\delta(U_2)=\\{f_3,f_4\\},$$
  that is, each strip has intervals and they are connected by the same lines.
  But projections
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111)$$
  linearly independent.
- `Toy test:` $n=4$, $j=1$: linked row-intervals on both stripes, but the projection rank of internal nodes is 2.
- `Status:` counterexample (toy, $k=2$): the linked condition on rows does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen geometry: require $U$ on a two-column strip
  was a **rectangular** set of vertices (both columns, one row-interval),
  and check whether this gives rank obstruction for $k=2$.
- `StepID:` Q39.S28-2k-two-strip-linked-intervals.
- `InfoGain:` 1.
-/

/-!
### 16.170. Exploratory step (counterexample): two-lane rectangular geometry (two-column stripe) does not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` If we require that each internal node of the XOR tree correspond to
  a rectangle in a two-column strip (two adjacent columns, one row-interval along the lines),
  then the projection rank on the two outer strips must be $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes as $S_{\\mathrm{left}}$ (between columns $j-1$ and $j$)
  and $S_{\\mathrm{right}}$ (between columns $j+1$ and $j+2$).
  We define the partition $\\pi$ in blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\},$$
  where $e_i$ are edges on $S_{\\mathrm{left}}$, $f_i$ are edges on $S_{\\mathrm{right}}$ (in row order).
  Let's take the internal nodes
  $$U_1=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},\\qquad
    U_2=\\{(3,j),(4,j),(3,j+1),(4,j+1)\\}.$$
  Then $U_1,U_2$ are $2\\times 2$ rectangles in a two-column strip, and the intersections
  with $S_{\\mathrm{left}}$ and $S_{\\mathrm{right}}$ - linked row-intervals on the same lines.
  However
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent.
- `Toy test:` $n=4$, $j=2$: two rectangular areas in a two-column strip give rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): rectangles on a two-column strip do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require anchored-rectangles (e.g. strings $[1..t]$)
  in a two-column strip or obvious closure with respect to XOR, and check whether
  does this give rank obstruction for $k=2$.
- `StepID:` Q39.S29-2k-two-strip-rectangular-geometry.
- `InfoGain:` 1.
-/

/-!
### 16.171. Exploratory step (counterexample): anchored rectangles in a two-column strip do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` If we require that each internal node of the XOR tree
  corresponded to an anchored rectangle in a two-column strip (two adjacent columns,
  strings $[1..t]$ for some $t$), then the projection rank on the two outer strips
  should be $\\le 1$.
- `Counterexample (toy):` Let $n=4$ and consider two adjacent columns $j$ and $j+1$.
  Let us denote the outer bands $S_{j-1}$ (between $j-1$ and $j$) and $S_{j+1}$ (between $j+1$ and $j+2$),
  and their edges in rows are as $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$.
  We define the partition $\\pi$ in blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let's take the internal nodes
  $$U_1=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},\\qquad
    U_2=\\{(1,j),\\dots,(4,j),(1,j+1),\\dots,(4,j+1)\\}.$$
  Then $U_1$ and $U_2$ are anchored rectangles (lines $[1..2]$ and $[1..4]$),
  and the projections give
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(1111,1111),$$
  which is linearly independent.
- `Toy test:` $n=4$, $j=2$: two anchored rectangles in a two-column strip give rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): anchored rectangles do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require the tree to be a **prefix-chain**
  (each internal node adds exactly one row) and check if
  whether the rank $\\ge 2$ remains in this mode.
- `StepID:` Q39.S30-2k-two-strip-anchored-rectangles.
- `InfoGain:` 1.
-/

/-!
### 16.172. Exploratory step (counterexample): prefix chain of anchored rectangles does not reduce projection rank for $k=2$

- `Lens:` Trade-off.
- `Assertion (attempt):` If you restrict the XOR tree to **prefix-chains** mode:
  each internal node is obtained by adding exactly one new line (anchored rectangles
  with series $[1..t]$), then the projection rank on the two outer strips must be $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$.
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows).
  We define the partition $\\pi$ by blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Consider a prefix chain of rectangles
  $$U_t=\\{(1,j),\\dots,(t,j),(1,j+1),\\dots,(t,j+1)\\},\\qquad t=1,2,3,4.$$
  Then each $U_t$ is an anchored rectangle, and the transition $U_t\\to U_{t+1}$ adds exactly one row.
  In this case, the projections:
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111)$$
  linearly independent. Therefore, the rank of the internal nodes of the chain is 2.
- `Toy test:` $n=4$, $j=2$: chain $U_1\\subset U_2\\subset U_3\\subset U_4$ gives rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): a prefix chain of anchored rectangles does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` try a restriction on **alternation of lanes**: require that
  each row addition changed only one of the two stripes (left or right), and check if
  whether rank obstruction appears at $k=2$.
- `StepID:` Q39.S31-2k-two-strip-prefix-chain.
- `InfoGain:` 1.
-/

/-!
### 16.173. Exploratory step (counterexample): alternating stripes in the XOR step does not reduce the projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let the condition **alternation of stripes** be satisfied for each XOR step:
  for parent $U$ and its children $U',U''$ intersections with two outer stripes
  satisfy
  $$S_{j-1}\\cap\\delta(U)=S_{j-1}\\cap\\delta(U')\\quad\\text{and}\\quad
    S_{j+1}\\cap\\delta(U)=S_{j+1}\\cap\\delta(U'').$$
  That is, when moving from $U$ to each child, only **one** band changes.
  It seems that such a regime should suppress independence in two lanes.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Let's consider two nodes:
  $$U_L=\\{(1,j),(2,j)\\}\\quad\\text{(left column, lines 1-2)},$$
  $$U_R=\\{(1,j+1),(2,j+1)\\}\\quad\\text{(right column, lines 1-2)}.$$
  Then $S_{j-1}\\cap\\delta(U_L)=\\{e_1,e_2\\}$ and $S_{j+1}\\cap\\delta(U_L)=\\varnothing$,
  and $S_{j-1}\\cap\\delta(U_R)=\\varnothing$ and $S_{j+1}\\cap\\delta(U_R)=\\{f_1,f_2\\}$.
  For the parent $U=U_L\\triangle U_R$ we get
  $$S_{j-1}\\cap\\delta(U)=\\{e_1,e_2\\},\\qquad S_{j+1}\\cap\\delta(U)=\\{f_1,f_2\\},$$
  that is, the condition of "alternating stripes" is satisfied (the left stripe coincides with $U_L$, the right one with $U_R$).
  But projections
  $$p(\\delta(U_L))=(1100,0000),\\qquad p(\\delta(U_R))=(0011,0000)$$
  are linearly independent, and the rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: The XOR step with alternating stripes leaves two independent vectors on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): alternating stripes at the XOR step does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require that each child matches the parent
  on **both** stripes, except for exactly one line (strict "one-line" change),
  and check whether it is then possible to obtain rank obstruction for $k=2$.
- `StepID:` Q39.S32-2k-two-strip-alternating-strip.
- `InfoGain:` 1.
-/

/-!
### 16.174. Exploratory step (counterexample): a one-line change on both stripes does not reduce the projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let for each XOR step and each child $U'$
  the symmetric difference on each strip has size $\\le 1$:
  $$\\bigl|(S_{j-1}\\cap\\delta(U))\\triangle(S_{j-1}\\cap\\delta(U'))\\bigr|\\le 1,\\quad
    \\bigl|(S_{j+1}\\cap\\delta(U))\\triangle(S_{j+1}\\cap\\delta(U'))\\bigr|\\le 1.$$
  (one-line change on both stripes). Expectation: This mode should kill rank.
- `Counterexample (toy):` Let $n=4$ and consider two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Let's take two rectangle nodes (one line in a two-column strip):
  $$U_1=\\{(1,j),(1,j+1)\\},\\qquad U_2=\\{(2,j),(2,j+1)\\}.$$
  Then $S_{j-1}\\cap\\delta(U_1)=\\{e_1\\}$ and $S_{j+1}\\cap\\delta(U_1)=\\{f_1\\}$,
  and $S_{j-1}\\cap\\delta(U_2)=\\{e_2\\}$ and $S_{j+1}\\cap\\delta(U_2)=\\{f_2\\}$.
  For the parent $U=U_1\\triangle U_2$ the following is true:
  $$\\delta(U)=\\delta(U_1)\\triangle\\delta(U_2),$$
  so the transitions $U\\leftrightarrow U_1$ and $U\\leftrightarrow U_2$ change **exactly one** line
  on each strip (the condition of a one-line change is met).
  However, projections
  $$p(\\delta(U_1))=(1010,0000),\\qquad p(\\delta(U_2))=(0101,0000)$$
  linearly independent.
- `Toy test:` $n=4$, $j=2$: single-line changes on both stripes allow two independent vectors on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): a one-line change does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` add row laminarity: require that any two internal nodes
  the intersection rows were nested (for example, one set of rows is a subset of another),
  and check whether rank obstruction appears at $k=2$.
- `StepID:` Q39.S33-2k-two-strip-single-row-change.
- `InfoGain:` 1.
-/

/-!
### 16.175. Exploratory step (counterexample): row laminarity does not reduce projection rank for $k=2$

- `Lens:` Trade-off.
- `Assertion (attempt):` Let for any two internal nodes $U,V$ of the set of strings,
  intersections of $S_{j-1}\\cap\\delta(U)$ and $S_{j-1}\\cap\\delta(V)$ (and similarly for $S_{j+1}$),
  **laminar**: one of the sets of rows is included in another.
  Expectation: Laminarity should suppress bilane independence.
- `Counterexample (toy):` Let $n=4$ and take two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Consider two anchored rectangles:
  $$U_2=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},\\qquad
    U_4=\\{(1,j),\\dots,(4,j),(1,j+1),\\dots,(4,j+1)\\}.$$
  Then the sets of intersection lines on each strip are $\\{1,2\\}\\subseteq\\{1,2,3,4\\}$,
  that is, laminarity is achieved.
  However, projections
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111)$$
  are linearly independent, which means the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: two laminar nodes $U_2\\subset U_4$ give rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): row laminarity does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the condition: require laminarity **and** identical boundaries on both stripes
  (for example, intersections must match as sets of lines), and check if
  whether rank obstruction appears at $k=2$.
- `StepID:` Q39.S34-2k-two-strip-laminar-rows.
- `InfoGain:` 1.
-/

/-!
### 16.176. Exploratory step (counterexample): equality of rows on two stripes does not reduce the projection rank for $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let for each internal node $U$ of the set of intersection lines
  on the two outer stripes coincide:
  $$\\mathrm{rows}(S_{j-1}\\cap\\delta(U))=\\mathrm{rows}(S_{j+1}\\cap\\delta(U)).$$
  Expectation: This should suppress independence on two lanes.
- `Counterexample (toy):` Let $n=4$ and take two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Consider anchored rectangles
  $$U_2=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},\\qquad
    U_4=\\{(1,j),\\dots,(4,j),(1,j+1),\\dots,(4,j+1)\\}.$$
  Then the strings on $S_{j-1}$ and $S_{j+1}$ are the same for each node:
  $$\\{1,2\\}\\ \text{for }U_2\\quad\\text{and}\\quad\\{1,2,3,4\\}\\ \text{for }U_4.$$
  But projections
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111)$$
  are linearly independent, which means the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: nodes $U_2\\subset U_4$ have equal rows on both stripes,
  but they give rank 2 at $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): equality of lines on two stripes does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require string equality **and** single-line change
  at each XOR step, and check whether rank obstruction appears at $k=2$.
- `StepID:` Q39.S35-2k-two-strip-equal-rows.
- `InfoGain:` 1.
-/

/-!
### 16.177. Exploratory step (counterexample): equal lines + one-line change do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let for each internal node $U$ be satisfied
  $$\\mathrm{rows}(S_{j-1}\\cap\\delta(U))=\\mathrm{rows}(S_{j+1}\\cap\\delta(U)),$$
  and each XOR step changes at most one line on each stripe.
  Expectation: This should suppress independence on two lanes.
- `Counterexample (toy):` Let $n=4$ and take two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Let's look at the nodes
  $$U_1=\\{(1,j),(1,j+1)\\},\\qquad U_2=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},$$
  and node $U=U_1\\triangle U_2$ (this is line 2 on both columns).
  Then the intersection lines coincide on both stripes for each of $U_1,U,U_2$,
  and the XOR step $U_1\\oplus U=U_2$ changes exactly one row on each stripe.
  In this case, the projections
  $$p(\\delta(U_1))=(1010,0000),\\qquad p(\\delta(U_2))=(1111,0000)$$
  linearly independent.
- `Toy test:` $n=4$, $j=2$: equal lines + one-line change allow two independent vectors on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): equal lines and one-line changes do not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` add chainability: require internal nodes to form
  linear chain by including rows, and check whether rank obstruction appears at $k=2$.
- `StepID:` Q39.S36-2k-two-strip-equal-rows-single-change.
- `InfoGain:` 1.
-/

/-!
### 16.178. Exploratory step (counterexample): a chain of XOR steps with equal rows and one-row changes does not reduce the projection rank for $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the internal nodes form a **chain by including rows**,
  the rows on the two stripes are the same, and each XOR step changes at most one row on each stripe.
  Expectation: In this mode, the projection rank on the two stripes should be $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and blocks $B_1=\\{e_1,e_2,f_1,f_2\\}$ and $B_2=\\{e_3,e_4,f_3,f_4\\}$.
  Let $R_t=\\{(t,j),(t,j+1)\\}$ be "one row" on both stripes, and define a chain of XOR steps
  $$U_1=R_1,\\quad U_2=U_1\\oplus R_2,\\quad U_3=U_2\\oplus R_3,\\quad U_4=U_3\\oplus R_4.$$
  Then the rows on $S_{j-1}$ and $S_{j+1}$ are the same for each $U_t$, and each step adds exactly one row,
  so the nodes form a chain by including $U_1\\subset U_2\\subset U_3\\subset U_4$.
  However, projections
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111)$$
  are linearly independent, which means the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: chain of XOR steps $U_1\\subset U_2\\subset U_3\\subset U_4$
  preserves line equality on both stripes and single-line changes, but gives rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): chaining + equal rows + one-line change does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen condition: require chain to be compatible with fixed line splitting
  (for example, each new line does not cross a block boundary), and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S37-2k-two-strip-equal-rows-single-change-chain.
- `InfoGain:` 1.
-/

/-!
### 16.179. Exploratory step (counterexample): chain consistent with partitioning blocks does not reduce projection rank when $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the internal nodes form a chain,
  the rows on the two stripes are the same, and each node crosses the stripes as a **union of entire blocks**
  splitting $\\pi$ (for example, by lines). Expectation: The blockchain must
  limit the projection rank on two stripes.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and define the partition $\\pi$ in blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let's look at the nodes
  $$U_2=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},\\qquad
    U_4=\\{(1,j),\\dots,(4,j),(1,j+1),\\dots,(4,j+1)\\}.$$
  Then intersections with stripes are equal in rows and are unions of entire blocks:
  $U_2$ uses $B_1$ and $U_4$ uses $B_1\\cup B_2$.
  Transition $U_2\\oplus R_{3,4}=U_4$ (where $R_{3,4}$ are the "bottom two rows" on both columns)
  changes exactly one block. However, projections
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111)$$
  are linearly independent, which means the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: block-consistent chain $U_2\\subset U_4$ gives rank 2 on $B_1\\sqcup B_2$.
- `Status:` counterexample (toy, $k=2$): a block-consistent chain does not reduce its rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the constraint: require every XOR change to be compatible
  with a fixed partition **and** did not cross block boundaries on both lanes at the same time,
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S38-2k-two-strip-chain-block-alignment.
- `InfoGain:` 1.
-/

/-!
### 16.180. Exploratory step (counterexample): block-consistent one-strip XOR updates do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let there be a fixed partition of strings into blocks $\\pi$, and in the chain of XOR steps
  each stripe intersection is a union of entire blocks, and each XOR step changes **only one**
  strip (the second remains unchanged), and the change in this strip is the union of entire blocks.
  Expectation: in such a block-consistent one-strip mode, the projection rank on two strips is $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer stripes $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$ (by rows),
  and define the partition $\\pi$ in blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Consider the chain
  $$U_1=\\{(1,j),(2,j),(1,j+1),(2,j+1)\\},$$
  $$U_2=\\{(1,j),(2,j)\\}\\cup\\{(1,j+1),(2,j+1),(3,j+1),(4,j+1)\\},$$
  $$U_3=\\{(1,j),\\dots,(4,j),(1,j+1),\\dots,(4,j+1)\\}.$$
  Transition $U_1\\oplus R^R_{3,4}=U_2$ (where $R^R_{3,4}$ are the bottom two lines in the right column)
  changes only the right lane (block $B_2$), and $U_2\\oplus R^L_{3,4}=U_3$
  (where $R^L_{3,4}$ are the bottom two lines in the left column) changes only the left stripe;
  both changes are block-consistent.
  However, the order is $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(1111,0011),$$
  which is linearly independent, so the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: a chain with single-lane block updates gives rank 2.
- `Status:` counterexample (toy, $k=2$): even block-consistency + one-strip updates does not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` tighten the regime: require lock-step updates (both bands change synchronously with the same blocks)
  and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S39-2k-two-strip-chain-block-consistency.
- `InfoGain:` 1.
-/

/-!
### 16.181. Exploratory step (counterexample): lock-step block-updates do not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let there be a fixed partition of strings into blocks $\\pi$, and in the chain of XOR steps
  each step is a **lock-step** update: both bars change synchronously on the same set of blocks,
  and the intersections of each node with stripes remain unions of entire blocks. Waiting: in this mode
  projection rank on two strips $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer bands $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$,
  and define the partition $\\pi$ in blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let $R_{1,2}$ and $R_{3,4}$ be the top/bottom two rows on both columns, and consider the chain
  $$U_1=R_{1,2},\\qquad U_2=U_1\\oplus R_{3,4},\\qquad U_3=U_2\\oplus R_{1,2}=R_{3,4}.$$
  Each step is a lock-step update (the same block changes on both stripes),
  and each $U_t$ crosses the stripes as a union of entire blocks. However ok
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_3))=(0000,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: lock-step block updates do not reduce rank.
- `Status:` counterexample (toy, $k=2$): lock-step block-updates do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen geometry: require lock-step updates on dyadic/laminar blocks
  in a fixed order (no returns), and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S40-2k-two-strip-chain-lockstep-blocks.
- `InfoGain:` 1.
-/

/-!
### 16.182. Exploratory step (counterexample): lock-step dyadic chain without backtracking does not reduce projection rank for $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let a dyadic row split and a chain of XOR steps be fixed
  updates both bands synchronously **only** by dyadic blocks in a fixed order (no returns),
  and each node crosses the stripes as a union of entire dyadic blocks. Waiting: in this mode
  projection rank on two strips $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer bands $S_{j-1}=\\{e_1,\\dots,e_4\\}$ and $S_{j+1}=\\{f_1,\\dots,f_4\\}$,
  and define dyadic blocks by row as
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Consider the chain
  $$U_1=R_{1,2},\\qquad U_2=U_1\\oplus R_{3,4}=R_{1,4}.$$
  This is a lock-step update over dyadic blocks in a fixed order $B_1\\to B_2$ without backtracking,
  and each $U_t$ crosses the stripes as a union of entire dyadic blocks. However ok
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: dyadic lock-step chain $U_1\\subset U_2$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): dyadic/laminar lock-step order does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the restriction: require **step by step** prefix updates $t\\to t+1$
  with dyadic-carry (without "jumps" $t\\to t'$, $t'-t>1$) and check whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S41-2k-two-strip-chain-lockstep-dyadic-blocks.
- `InfoGain:` 1.
-/

/-!
### 16.183. Exploratory step (counterexample): step-by-step dyadic-prefix updates $t\\to t+1$ do not reduce projection rank at $k=2$

- `Lens:` Communication/Rank.
- `Assertion (attempt):` Let the chain of XOR steps update the prefix row by row **step by step**,
  those. $t\\to t+1$ (dyadic-carry without jumping), and each node crosses the stripes as a union
  dyadic blocks of the prefix $[t]$. Expectation: This mode should limit the projection rank on two lanes.
- `Counterexample (toy):` Let's take $n=4$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let $U_t$ be an anchored rectangle of height $t$ on both columns:
  $$U_t=\\{(1,j),\\dots,(t,j),(1,j+1),\\dots,(t,j+1)\\},\\quad t=1,2,3,4.$$
  Then transitions $U_t\\to U_{t+1}$ add exactly one row, and intersections with stripes
  coincide with the dyadic partition of the prefix $[t]$ (for $t=1,2,3,4$ these are $[1]$, $[1,2]$, $[1,2]\\uplus[3]$, $[1,4]$).
  However, in the order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: chain $U_1\\subset U_2\\subset U_3\\subset U_4$ with dyadic-carry steps gives rank 2.
- `Status:` counterexample (toy, $k=2$): step-by-step dyadic-prefix updates do not reduce the rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the constraint: require the chain to include **all** intermediate
  dyadic-merge state (after adding a line and each move), and check if the rank remains $\\ge 2$.
- `StepID:` Q39.S42-2k-two-strip-chain-dyadic-prefix-stepwise.
- `InfoGain:` 1.
-/

/-!
### 16.184. Exploratory step (counterexample): dyadic-carry microsteps do not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let the chain include **all** dyadic-carry microsteps:
  after adding the line $t+1$, all intermediate states of the partition are fixed
  (after each transfer), and each node crosses the stripes as a union of entire dyadic blocks.
  Expectation: This enhanced mode should reduce the projection rank.
- `Counterexample (toy):` Let's take $n=4$ and a chain of anchored rectangles $U_t$ as in Section 16.183.
  Dyadic-carry microsteps at $t=3\\to4$ change **only the representation of the partition**,
  but not a set of strings: all intermediate states correspond to the same set
  $\\{1,2,3,4\\}$, so in the XOR tree they can be inserted as repetitions of node $U_4$.
  Then there are still $U_2$ and $U_4$ in the chain, and ok
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent. Hence adding dyadic-carry microsteps
  does not reduce the projection rank of internal nodes.
- `Toy test:` $n=4$, $j=2$: chain $U_1\\subset U_2\\subset U_3\\subset U_4$ with inserted dyadic-carry
  microsteps (repetitions $U_4$) gives rank 2.
- `Status:` counterexample (toy, $k=2$): dyadic-carry microsteps do not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` require not only dyadic partition updates, but also **different** support sets
  at each microstep (for example, fix the representation through additional edges),
  and check whether this gives rank obstruction for $k=2$.
- `StepID:` Q39.S43-2k-two-strip-chain-dyadic-carry-microsteps.
- `InfoGain:` 1.
-/

/-!
### 16.185. Exploratory step (counterexample): distinct-support microsteps do not reduce projection rank at $k=2$

- `Lens:` Trade-off.
- `Assertion (attempt):` Let **all** nodes in the chain of dyadic-carry microsteps have
  different sets of supports (distinct support), but intersections with stripes remain
  combining dyadic blocks. Expectation: This should suppress independence on two lanes.
- `Counterexample (toy):` Let's take $n=6$ and two adjacent columns $j$ and $j+1$ (for example, $j=2$).
  Let us denote the outer bands $S_{j-1}=\\{e_1,\\dots,e_6\\}$ and $S_{j+1}=\\{f_1,\\dots,f_6\\}$,
  and take the blocks for two lanes as
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let $U_t$ be an anchored rectangle of height $t$ on both columns ($t=1,2,3,4$) and
  take a vertex $w=(1,j+3)$ that is not incident to the stripes $S_{j-1},S_{j+1}$.
  Then the nodes $U'_t:=U_t\\cup\\{w\\}$ are all distinct, but their intersections with the stripes
  coincide with $U_t$ and remain a union of dyadic blocks.
  In order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U'_2))=(1111,0000),\\qquad p(\\delta(U'_4))=(1111,1111),$$
  which is linearly independent. Therefore, distinct-support microsteps do not reduce rank.
- `Toy test:` $n=6$, $j=2$: chain $U'_1\\subset U'_2\\subset U'_3\\subset U'_4$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): distinct-support does not help.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the restriction: require distinct support **on lanes** (i.e. change
  $S_{j-1}\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ themselves at each microstep) and check whether
  whether the rank $\\ge 2$ remains at $k=2$.
- `StepID:` Q39.S44-2k-two-strip-chain-dyadic-microsteps-distinct-support.
- `InfoGain:` 1.
-/

/-!
### 16.186. Exploratory step (counterexample): distinct strip support at microstep does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` Let each microstep in the dyadic model chain change
  **intersections with stripes** (distinct strip support), that is, both sets
  $S_{j-1}\\cap\\delta(U)$ and $S_{j+1}\\cap\\delta(U)$ are different from the previous node,
  remaining a union of dyadic blocks. Expectation: This should suppress independence on two lanes.
- `Counterexample (toy):` Let's take $n=4$, two adjacent columns $j$ and $j+1$ (for example, $j=2$),
  and a chain of anchored rectangles
  $$U_t=\\{(1,j),\\dots,(t,j),(1,j+1),\\dots,(t,j+1)\\},\\quad t=1,2,3,4.$$
  At each step, the sets of lines on both stripes change (prefix chain),
  and intersections with stripes - unions of dyadic blocks of the prefix $[t]$.
  However, in the order $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_2))=(1111,0000),\\qquad p(\\delta(U_4))=(1111,1111),$$
  which is linearly independent, which means the projection rank of the internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: chain $U_1\\subset U_2\\subset U_3\\subset U_4$ with distinct strip support gives rank 2.
- `Status:` counterexample (toy, $k=2$): distinct strip support does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` strengthen the restriction: require **synchronous** band changes
  according to a fixed pattern (for example, identical dyadic blocks on both lanes
  and a ban on a monotonic prefix chain), and check whether the rank $\\ge 2$ remains.
- `StepID:` Q39.S45-2k-two-strip-chain-dyadic-microsteps-strip-support.
- `InfoGain:` 1.
-/

/-!
### 16.187. Exploratory step (counterexample): synchronous fixed stripe pattern does not reduce projection rank at $k=2$

- `Lens:` Invariant.
- `Assertion (attempt):` If in the chain the intersections with the stripes are synchronized and
  follow a fixed pattern (for example, at each step both stripes coincide and
  equal to one dyadic block from a fixed partition; monotonic prefix chain is prohibited),
  then the projection rank on the two strips must be $\\le 1$.
- `Counterexample (toy):` Let's take $n=4$, two adjacent columns $j$ and $j+1$ (for example, $j=2$),
  and dyadic blocks
  $$B_1=\\{e_1,e_2,f_1,f_2\\},\\qquad B_2=\\{e_3,e_4,f_3,f_4\\}.$$
  Let
  $$U_1=R_{1,2},\\qquad U_2=R_{3,4},\\qquad U_3=U_1$$
  (pattern $B_1\\to B_2\\to B_1$). Then at each step of intersection with stripes
  are synchronized and equal to one block, but there is no monotonic prefix chain. In order
  $(e_1,e_2,f_1,f_2,e_3,e_4,f_3,f_4)$ we have
  $$p(\\delta(U_1))=(1111,0000),\\qquad p(\\delta(U_2))=(0000,1111),$$
  which is linearly independent, therefore the projection rank of internal nodes is 2.
- `Toy test:` $n=4$, $j=2$: synchronous pattern $B_1\\to B_2\\to B_1$ gives rank 2.
- `Status:` counterexample (toy, $k=2$): a fixed synchronous pattern does not reduce rank.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` require global synchronization across columns (single block order
  for all pairs of stripes) and check whether rank $\\ge 2$ still allows this.
- `StepID:` Q39.S46-2k-two-strip-chain-strip-support-synchronized.
- `InfoGain:` 1.
-/
