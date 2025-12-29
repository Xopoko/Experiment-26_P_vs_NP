import Paperproof

/-!

#P vs NP - Research Steps 16.85-16.121 (Tseitin: Basic Facts and Boundaries)

Main index: `P_vs_NP.md`.

### 16.85. Exploratory step: Tseitin($G,\chi$) and parity certificate of insatisfiability

- `Lens:` Invariant.
- `Definition:` Let $G=(V,E)$ be an undirected graph and $\chi:V\to\{0,1\}$
  ("charges"). Each edge $e\in E$ is associated with a Boolean variable $x_e$.
  The Tseitin XOR system is given by modulo 2 equations:
  $$\bigoplus_{e\ni v} x_e\ =\ \chi(v)\qquad\text{for all }v\in V.$$
- `Statement:` If for some connected component $H\subseteq G$ we have
  $\bigoplus_{v\in V(H)}\chi(v)=1$, then the system (and hence any CNF/3CNF
  encoding these XOR constraints) is not feasible.
- `Proof:` Let us take XOR over all vertices $v\in V(H)$ from the left sides.
  Each variable $x_e$ (for an edge $e$ inside $H$) appears exactly twice - each
  ends of the edge - and therefore cancels: $\bigoplus_{v\in V(H)}\bigoplus_{e\ni v}x_e=0$.
  Then the equations imply $0=\bigoplus_{v\in V(H)}\chi(v)=1$, a contradiction.
- `3CNF encoding for 3regular $G$:` if $\deg(v)=3$ and incident edges
  have variables $a,b,c$, then the constraint $a\oplus b\oplus c=\chi(v)$ is equivalent
  3CNF of 4 clauses (we prohibit 4 triples that do not match in parity). Therefore, when
  3regular $G$ we obtain a 3CNF of size $4|V|$, and each variable $x_e$ is included
  exactly $8$ clauses ($4$ at each end of the edge).
- `Toy test:` one edge $e=\{u,v\}$ and $\chi(u)=1,\chi(v)=0$ gives the system
  $x_e=1$ and $x_e=0$ (obvious impossibility); parity argument above is exactly this
  fixes as $\chi(u)\oplus\chi(v)=1$.
- `Status:` proven (parity invariant) + explicit 3CNF for $\Delta=3$.
- `Barrier check:` r -- applicable (trivially relativized), NP -- not applicable
  (no "natural property"), alg - not applicable.
- `Next step:` state in the main text what the family provides
  infeasible 3CNF with boundedocc on 3regular expanders, and bind
  to known resolution lower bounds (via expansion/width).

### 16.86. Exploratory step: expansion  resolution width/size for Tseitin on boundeddegree graphs

- `Lens:` Trade-off.
- `Statement:` Let $G=(V,E)$ be a connected graph of maximum degree $\le k$, and
  $e(G):=\min_{A\subseteq V,\ |V|/3\le |A|\le 2|V|/3}|E(A,\bar A)|$ is its expansion
  (Itsykson-Oparin 2013, Def. 2). If Tseitin($G,\chi$) is not satisfiable, then the width
  resolution refutation is satisfied by $W(\mathrm{Tseitin}(G,\chi)\vdash 0)\ge e(G)-1$
  (Itsykson-Oparin 2013, Cor. 1). Then by tradeoff "width  size"
  (Ben-Sasson-Wigderson 2001; also formulated as Thm. 1 in Itsykson-Oparin 2013)
  we obtain for the number of variables $n:=|E|$ (where $S$ is the size of the dagresolution, and $ST$ is the size of the treelike resolution):
  $$S(\mathrm{Tseitin}(G,\chi))\ \ge\ 2^{\Omega\!\left(\frac{(e(G)-k-1)^2}{n}\right)},\qquad
    ST(\mathrm{Tseitin}(G,\chi))\ \ge\ 2^{\,e(G)-k-1}.$$
  In particular, for a family of graphs of degree $O(1)$ with $e(G)=\Omega(|V|)$ (expanders)
  we have $n=\Theta(|V|)$ and therefore $S\ge 2^{\Omega(|V|)}$.
- `Toy test:` cycle $C_n$ has $e(C_n)=2$, which means the estimate gives only a constant
  bottom border on width/size; this is consistent with the fact that "bad" expansion
  should not give strong lower marks.
- `Status:` proven (quote Cor. 1 + standard width-size tradeoff).
- `Barrier check:` r--not applicable (model-specific lower bound),
  NP - not applicable, alg - not applicable.
- `Next step:` apply to 3regular expanders and 3CNF encoding from Section 16.85,
  to obtain an explicit bounded-occ 3-CNF family with exponential resolution.

### 16.87. Exploratory step: explicit bounded-occ Tseitin-family on 3-regular expanders

- `Lens:` Equivalence.
- `Statement:` There is a strongly explicit family of 3-regular expanders
  $\{G_n\}$ with $\lambda(G_n)\le \lambda_0<1$ (for example, a family of Ramanujan graphs;
  see discussion in `../../resources/downloads/arora_barak.pdf`, §16.3, Remark 16.10).
  Then, according to the connection between spectral and combinatorial expansion (Arora-Barak, Thm. 16.18)
  we have $|E(A,\bar A)|\ge \rho d|A|$ for all $|A|\le |V|/2$ and some constant
  $\rho>0$, whence $e(G_n)=\Omega(|V_n|)$ in the sense of Def. 2 from Itsykson-Oparin.
  Let $\chi_n$
  has an odd sum of charges, and $F_n$ is the 3CNF encoding of Tseitin($G_n,\chi_n$) from Section 16.85.
  Then:
  (i) $F_n$ is unsatisfiable; (ii) $|F_n|=\Theta(|V_n|)$; (iii) boundedocc = 8;
  (iv) the size of the resolution refutation $S(F_n)=2^{\Omega(|V_n|)}$ (according to Section 16.86).
- `Toy test:` if $G$ is a cycle, then $e(G)=2$ and Section 16.86 gives only constant bounds;
  on the expander $e(G)=\Omega(|V|)$ and for $|E|=\Theta(|V|)$ we obtain the exponential
  $\Omega(|V|)$ in the lower bound on $S(F)$.
- `Status:` proven (composition 16.85 + 16.86 + existence of expander family).
- `Barrier check:` r--not applicable (model-specific lower bound),
  NP - not applicable, alg - not applicable.
- `Next step:` clarify/fix a specific link to the selected explicit
  3regular expander family (if necessary) and note which systems
  evidence (PC/EF) remains open on these formulas.

### 16.88. Research step: Tseitin is easy in EF; PC depends on field/basis

- `Lens:` Algebraization.
- `Statement:` Let $G$ be connected and $\bigoplus_{v\in V}\chi(v)=1$. Then 3CNF
  the encoding $F=\mathrm{TseitinCNF}(G,\chi)$ from Section 16.85 has a polynomial
  refutation in Extended Frege (EF), since
  a contradiction gives the summation of XOR equations modulo 2. For Polynomial
  Calculus: above characteristic field 2 the corresponding linear system
  refuted to the degree of 1; over $\mathrm{char}(F)\ne 2$ in the Fourier basis are known
  linear degree lower bounds (Beame-Sabharwal 2000, Thm. 2.18).
- `Proof (EF framework):`
  Let us denote $a\oplus b := (a\wedge\neg b)\vee(\neg a\wedge b)$.
  Associativity/commutativity identities and reductions
  $a\oplus(a\oplus b)\leftrightarrow b$, $a\oplus a\leftrightarrow 0$
  have a constant size (3 variables)  constant Frege pins.
  For each vertex $v$ of degree 3, with incident edges $e_1,e_2,e_3$,
  The 4 clauses in Section 16.85 are equivalent to the formula
  $$(x_{e_1}\oplus x_{e_2}\oplus x_{e_3})\leftrightarrow \chi(v)$$
  (check 8 values; constant output).
  In EF we introduce extension variables $p_v\leftrightarrow (x_{e_1}\oplus x_{e_2}\oplus x_{e_3})$
  and $P\leftrightarrow\bigoplus_{v\in V} p_v$ (XOR chain/tree, size $O(|V|)$).
  From the previous we obtain $P\leftrightarrow\bigoplus_v\chi(v)$, which means $P$.
  On the other hand, substituting the definitions of $p_v$ and using local
  permutations/XOR brackets (polynomial many steps), we get
  $$P\leftrightarrow\bigoplus_{v\in V}\ \bigoplus_{e\ni v} x_e\ \leftrightarrow\ \bigoplus_{e\in E}(x_e\oplus x_e)\ \leftrightarrow\ 0,$$
  contradiction.
- `Link (EF  XOR/Gauss):` noted that EF "easily simulates Gaussian elimination"
  (and therefore proves linear-algebraic statements polynomially),
  see Bonet-Buss-Pitassi 2002, `../../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf` (p. 7).
- `PC note:` If we consider Tseitin as a linear system over $\mathbb F_2$,
  $$\sum_{e\ni v} x_e = \chi(v)\quad(\bmod 2),$$
  then in PC over $\mathbb F_2$ the refutation is obtained to the power of 1: we sum
  equations in $v\in V$, we obtain $0=\bigoplus_v\chi(v)=1$.
- `Known fact (PC, $\mathrm{char}(F)\ne 2$):` for any sequence boundeddegree
  graphs $\{G_n\}$ with $c(G_n)=\Omega(1)$ (expanders) any PC-refutation
  $\mathrm{Tseitin}(G_n)$ over a field of odd or zero characteristic has degree
  $\Omega(|V_n|)$, and according to the degree->size connection the size is also $2^{\Omega(|V_n|)}$
  (Razborov 2023, Thm. 6.8 + paragraph after Thm. 6.9).
- `Toy test:` $G=C_3$ and $\chi\equiv 1$. The sum of the three equations gives
  $(x_{12}\oplus x_{12})\oplus(x_{23}\oplus x_{23})\oplus(x_{31}\oplus x_{31})=1$,
  that is, $0=1$.
- `Status:` EFupper bound - proven as a scheme; for PC over $\mathbb F_2$ - proven;
  for $\mathrm{char}(F)\ne 2$ the degree and size are known lower bounds (see the fact above).
- `Barrier check:` r - not applicable (statement about specific proof systems),
  NP - not applicable, alg - not applicable.
- `Next step:` see Section 16.89 (clause form TseitinCNF is easy in PC over $\mathbb F_2$);
  Next - understand whether (and how) degree-LB for $\mathrm{char}(F)\ne 2$ is transferred from the XOR-system
  to 3CNF encoding.

### 16.89. Exploratory step: TseitinCNF easy in PC over $\mathbb F_2$ (degree 3)

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a 3regular graph, $\chi:V\to\{0,1\}$ and
  $\bigoplus_{v\in V}\chi(v)=1$. Let $F=\mathrm{TseitinCNF}(G,\chi)$ be the 3CNF from Section 16.85.
  Then over the field $\mathbb F_2$ there exists a Polynomial Calculus-refutation $F$ of degree $\le 3$
  and size $O(|V|)$.
- `Proof (local linear form):`
  We translate the clause $(\ell_1\vee \ell_2\vee \ell_3)$ into a polynomial equation
  $$(1-\ell_1)(1-\ell_2)(1-\ell_3)=0,$$
  where the literal $\neg x$ is interpreted as $1-x$ (the Boolean axioms $x^2-x=0$ are not needed).
  Let us fix a vertex $v$ of degree 3 with incident edges $e_1,e_2,e_3$ and denote
  $x_i:=x_{e_i}$.
  - If $\chi(v)=1$, then 4 clauses from Section 16.85 give 4 axioms:
    $$(1-x_1)(1-x_2)(1-x_3)=0,\ (1-x_1)x_2x_3=0,\ x_1(1-x_2)x_3=0,\ x_1x_2(1-x_3)=0.$$
    Adding them into $\mathbb F_2$, we get $1+x_1+x_2+x_3=0$, that is, $x_1+x_2+x_3+\chi(v)=0$.
  - If $\chi(v)=0$, then similarly from 4 clauses we obtain the axioms:
    $$(1-x_1)(1-x_2)x_3=0,\ (1-x_1)x_2(1-x_3)=0,\ x_1(1-x_2)(1-x_3)=0,\ x_1x_2x_3=0,$$
    and their sum is $x_1+x_2+x_3=0$, that is, again $x_1+x_2+x_3+\chi(v)=0$.

  So, for each $v$ the linear equation is derived
  $$\sum_{e\ni v} x_e\ +\ \chi(v)\ =\ 0\quad(\text{in }\mathbb F_2).$$
  Adding these equations over all $v\in V$, we obtain
  $$\sum_{v\in V}\sum_{e\ni v}x_e\ +\ \sum_{v\in V}\chi(v)=0.$$
  Each variable $x_e$ appears on the left side exactly twice (at the ends of the edge), which means
  in $\mathbb F_2$ cancels, and $\sum_v\chi(v)=0$ remains, that is, $1=0$--a contradiction.
  Degree of proof $\le 3$ (all clause axioms are degree 3), number of lines $O(|V|)$.
- `Toy test:` $G=C_3$ and $\chi\equiv 1$. For each vertex a linear equation is derived
  along three edges, the sum of the three equations gives $1=0$.
- `Status:` proven (explicit local derivation + summation over the graph).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` formulate the same "local translation" for $\mathrm{char}(F)\ne 2$
  (or find a link) to link TseitinCNF with well-known degreeLB for PC.

### 16.90. Exploratory step: TseitinCNF $\leftrightarrow$ binomial Tseitin in PC for $\mathrm{char}(F)\ne 2$

- `Lens:` Equivalence.
- `Statement:` Let $F$ be a field, $\mathrm{char}(F)\ne 2$, and $v$ a degree 3 vertex
  with incident variables $x_1,x_2,x_3\in\{0,1\}$ and charge $\chi\in\{0,1\}$.
  Let 4 clauses TseitinCNF($v$) be a standard 3CNF constraint encoding
  $x_1\oplus x_2\oplus x_3=\chi$ (as in Section 16.85), translated into PC axioms of the form
  $(1-\ell_1)(1-\ell_2)(1-\ell_3)=0$. Then:
  1) from these 4 clauses in PC one equation of degree 3 is derived
     $$X(x_1,x_2,x_3)-\chi=0,$$
     Where
     $$X(x_1,x_2,x_3):=x_1+x_2+x_3-2(x_1x_2+x_1x_3+x_2x_3)+4x_1x_2x_3;$$
  2) with linear replacement $y_i:=1-2x_i$ this is equivalent to the binomial equation
     $$y_1y_2y_3-(1-2\chi)=0\quad(\text{and }y_i^2-1=0);$$
  3) on the contrary, from $X-\chi=0$ in PC all 4 clause axioms with constant
     loss of degree (<=6). Therefore, for 3regular graphs TseitinCNF and
     "binomial" Tseitin (Fourier/1base) pequivalent in degree in PC.
     In particular, degree/size lower bounds for the binomial Tseitin for $\mathrm{char}(F)\ne 2$
     (Razborov 2023, Thm. 6.8; see also Beame-Sabharwal 2000, Thm. 2.18) are carried over to TseitinCNF.

- `Proof (1, locally):`
  In $\mathbb F[x_1,x_2,x_3]/(x_i^2-x_i)$ each clause axiom for a vertex of degree 3 is
  this is an indicator of a forbidden assignment (a monomial of degree 3 in the literals $x_i$ and $(1-x_i)$).
  For $\chi=0$ 4 odd triplets are prohibited, and the sum of 4 indicators is equal to exactly $X$.
  For $\chi=1$ 4 even triplets are prohibited, and the sum of the indicators is $1-X$.
  In both cases, from the 4 equalities "indicator = 0" the output is $X-\chi=0$
  (for $\chi=1$ by multiplying by $-1$).

- `Proof (2):`
  Opening the brackets
  $$(1-2x_1)(1-2x_2)(1-2x_3)=1-2X(x_1,x_2,x_3).$$
  That's why
  $$y_1y_2y_3-(1-2\chi)=(1-2X)-(1-2\chi)=-2(X-\chi),$$
  that is, the equations differ by a nonzero scalar.

- `Proof (3, locally):`
  Let $m_{a_1a_2a_3}:=\prod_i (x_i)^{a_i}(1-x_i)^{1-a_i}$ be an assignment indicator to $(a_1,a_2,a_3)$.
  If $(a_1\oplus a_2\oplus a_3)\ne\chi$, then on this assignment $X-\chi=\pm 1$, and on the rest
  $m_{a_1a_2a_3}=0$, which means that in the factor algebra it is identical
  $$(X-\chi)\,m_{a_1a_2a_3}=\pm m_{a_1a_2a_3}.$$
  From $X-\chi=0$, according to the multiplication rule, we obtain $(X-\chi)m_{a_1a_2a_3}=0$, whence $m_{a_1a_2a_3}=0$.
  This is exactly one of the 4 TseitinCNF($v$) clauses. Degree: $\deg(X-\chi)\le 3$, $\deg(m)\le 3$, total <=6.

- `Toy test:` $\chi=1$. The sum of 4 "even" indicators (000,011,101,110) is equal to $1-X$,
  that means they imply $X-1=0$, and then $y_1y_2y_3+1=0$.
- `Status:` proven (local p-equivalence in degree for $\mathrm{char}(F)\ne 2$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary for the main text, add a 1-line remark in 15.x:
  "at $\mathrm{char}(F)\ne 2$ TseitinCNF inherits PC degree/sizeLB through 16.90."

### 16.91. Exploratory step: Tseitin has polynomial Frege refutations (Urquhart 1987)

- `Lens:` Equivalence.
- `Statement:` Let $G$ be connected and $\bigoplus_{v\in V}\chi(v)=1$; let $\mathrm{TseitinCNF}(G,\chi)$ be a clause
  form of equations modulo 2 (as in Section 16.85 for $\deg(G)=3$, or in general form via $2^{\deg(v)-1}$ clause to the vertex).
  Then $\mathrm{TseitinCNF}(G,\chi)$ has a polynomial refutation in the usual Frege (in particular,
  in "Kleene's axiomatic system", i.e. Hilbertstyle propositional calculus): Urquhart (1987) gives
  explicit derivation of length $O(n^4)$ (where $n=\Theta(|V|)$ for boundeddegree).
- `Proof (idea from Urquhart 1987, Lemma 6.1):`
  1) for each vertex $v$ the corresponding XOR equation is restored from the encoding clause
     (Urquhart has "biconditional"/equivalence that fixes the parity of literals at the top);
  2) these equivalences are "glued together" into one large expression; then using
     associativity/commutativity, paired occurrences of variables "pop up" and are reduced;
  3) a contradiction remains, since the left side cancels to $0$, and the right side gives
     $\bigoplus_v\chi(v)=1$.
  Details: Urquhart 1987, Section 6, Lemma 6.1, `../../resources/downloads/urquhart_1987_hard_examples_resolution.pdf`.
- `Toy test:` $G=C_3$, $\chi\equiv 1$: three local XOR equations sum to $0=1$
  (See also toy test in Section 16.88).
- `Status:` proven (top score/link).
- `Barrier check:` r - not applicable (this is the upper bound in the fixed proof model),
  NP - not applicable, alg - not applicable.
- `Next step:` clarify the "minimum depth" of polynomial Frege refutations of Tseitin:
  fix the best known depthvssize estimate (reference to the work of the Hastad'17/18 level and/or subsequent enhancements).

### 16.92. Exploratory step: depthvssize for Tseitin(Grid) in boundeddepth Frege (Hastad 2020)

- `Lens:` Trade-off.
- `Statement:` Let us consider the Tseitin contradiction on a $n\times n$ grid.
  If $d\le \frac{\log n}{59\log\log n}$, then any depth$d$ Fregerefutation has the size
  $2^{\Omega(n^{1/(58(d+1))})}$ (Håstad 2020, Thm. 6.5; `../../resources/downloads/hastad_2020_small_depth_frege_tseitin_grids.pdf`,
  `exp` in source = $2^x$).
  In particular, any polynomial
  by $n$ (and therefore by the number of variables $N=\Theta(n^2)$) Frege-refutation requires depth formulas
  $\Omega(\log n/\log\log n)$ (Håstad 2020, Cor. 6.6).
- `Toy test:` with constant depth $d=O(1)$ we obtain a superpolynomial lower bound
  $2^{\Omega(n^{\Omega(1)})}=2^{\Omega(N^{\Omega(1)})}$ for Tseitin(Grid$_{n,n}$).
- `Status:` known fact (exact link).
- `Barrier check:` r - not applicable (lower estimate for a limited evidence model),
  NP - not applicable, alg - not applicable.
- `Next step:` compare with the "upper" estimate $O(\log n)$ of depth for polysize Fregerefutations Tseitin
  (Buss-style score/parity) and record how tight the gap $O(\log\log n)$ remains.

### 16.93. Exploratory step: $O(\log n)$ depth upper bound for polysize Frege on Tseitin (boundeddegree)

- `Lens:` Compression/canonization.
- `Statement:` For Tseitin-contradiction on any bounded-degree graph (clause form of parity equations)
  there is a polynomial in $n$ Frege inference using $O(\log n)$ depth formulas in the standard language
  $L_\\in=\\{\\wedge,\\vee,\\neg\\}$.
- `Proof:` we take the polynomialsize Fregerefutation $\\pi$ from Urquhart (1987) (see Section 16.91).
  Then we apply Spira balancing to each line $A$ of $\\pi$ (Bonet-Buss 2002, Thm. 2; see Section 16.94),
  obtaining the equivalent formula $A'$ of depth $O(\\log|A|)$ and size $\\mathrm{poly}(|A|)$.
  According to Section 16.114, for this balancing there are polynomialsize Fregeproofs of the tautologies $A\\leftrightarrow A'$,
  and by Section 16.113, from $A$ and $A\\leftrightarrow A'$ one derives $A'$ with $O(1)$ additional lines.
  Replacing the lines by induction, we obtain a Frege refutation $\\pi'$ of the same CNF, where all lines have depth $O(\\log n)$,
  and the overall blow-up remains polynomial (since the original size $\\pi$ is polynomial in $n=\\Theta(|\\mathrm{TseitinCNF}(G,\\chi)|)$ for bounded-degree).
- `Toy test:` on the loop you can write a balanced formula for XOR of all equations and reduce paired occurrences of edges,
  getting $0=1$ for an odd sum of charges.
- `Status:` proven (via Section 16.91+Section 16.94+Section 16.113-Section 16.114).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether the upper estimate from 16.97 (GIRS'19, Thm. 19) gives a polynomialsize already at depth
  $\\Theta(\\log n/\\log\\log n)$ on the lattices/expanders, thereby closing the gap from 16.92.

### 16.94. Exploratory step: balancing formulas  you can require $O(\log n)$ depth in Frege

- `Lens:` Trade-off.
- `Statement:` Any Boolean formula of size $m$ is equivalent to a formula of depth $O(\log m)$
  (Brent/Spira restructuring). Exact link: Bonet-Buss (2002), Theorem 2 (Spira),
  `../../resources/downloads/bonet_buss_2002_size_depth_tradeoffs_boolean_formulae.pdf`.
  Therefore, if $\mathrm{TseitinCNF}(G,\chi)$ has a polynomial-size Frege-refutation
  (16.91, Urquhart 1987), then we can assume that all large intermediate formulas
  in this refutation are balanced to a depth of $O(\log n)$ (with polynomial blow-up),
  those. the upper bound $O(\log n)$ in depth does not require a separate "countable" construction.
- `Toy test:` a long chain of disjunctions/biimplications of length $m$ has depth $\Theta(m)$,
  but after balancing the depth becomes $O(\log m)$.
- `Status:` proven (line replacement: Section 16.113; p-equivalence proofs for Spira balancing: Section 16.114).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` use 16.94+16.95 as a "pure" upper estimate for depth and return to the lower estimates (16.92, 16.97).

### 16.95. Research step: UrquhartTseitin + Spiratranslation  $O(\log n)$depth Frege (strictly)

- `Lens:` Equivalence.
- `Statement:` Let there be a Frege refutation of the formula $\Phi$ in the language $L_\infty$, where, in particular,
  $\{\wedge,\oplus,\neg\}$ or $\{\equiv,\oplus\}$ (as in Urquhart 1987 for "biconditionals").
  Then there is a polynomial-in-size Frege refutation of $\Phi'$ in the standard language
  $L_\in=\{\wedge,\vee,\neg\}$, and the translation $\phi\mapsto\phi'$ is arranged in such a way that:
  (i) $\phi'$ is equivalent to $\phi$ (in meaning); (ii) the depth $\phi'$ is $O(\log|\phi|)$ (Spirarebalancing);
  (iii) the size of $\phi'$ is polynomial in $|\phi|$. Reference: Buss (1997), Theorem 3 + proof-sketch
  «indirect translation via Spira», `../../resources/downloads/buss_1997_proof_complexity_intro.pdf`.
  Corollary: for boundeddegree $\mathrm{TseitinCNF}(G,\chi)$ (odd sum of charges) there exists
  polynomialsize Fregerefutation using depth formulas $O(\log n)$: take
  Urquhart (1987) (16.91) and use the Buss'97/Spira translation.
- `Toy test:` if you do a "direct translation" $\phi_1\oplus\phi_2\mapsto(\phi_1\wedge\neg\phi_2)\vee(\neg\phi_1\wedge\phi_2)$
  recursively along linear depth, then the size can become exponential; Spira translation
  "re-balances" the tree and keeps the size polynomial (Buss'97, Proof sketch for Thm. 3).
- `Status:` known fact (technical part for 16.94/question Q14 is closed).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` use this as a "pure" justification for the $O(\log n)$ upper bound on depth and
  further improve the lower estimates (narrow the gap from 16.92).

### 16.96. Exploratory step: Tseitin on expanders - depthvssize (Pitassi-Rossman-Servedio-Tan 2016)

- `Lens:` Trade-off.
- `Statement:` There is a linear size 3CNFcontradiction $\mathrm{Tseitin}(G_n[\alpha])$
  on a 3regular $n$vertex expander such that for any $d$ any depth$d$ Fregerefutation
  has size $n^{\Omega((\log_2 n)/d^2)}$ (Pitassi-Rossman-Servedio-Tan 2016, Thm. 1,
  `../../resources/downloads/pitassi_rossman_servedio_tan_2016_expander_switching_lemma.pdf`).
  Consequently, any polynomial-size Frege-refutation requires a depth of $d=\Omega(\sqrt{\log_2 n})$.
- `Toy test:` if $d=O(1)$, then the lower bound gives the size $2^{\Omega((\log_2 n)^2)}=n^{\Omega(\log_2 n)}$ (quasi-poly),
  and if $d=\Theta(\sqrt{\log_2 n})$, then the exponent $(\log_2 n)/d^2=\Theta(1)$ and the estimate ceases to be superpolynomial.
- `Status:` known fact (exact link).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` match 16.96 (expander: $\sqrt{\log n}$) with 16.92 (grid: $\log n/\log\log n$)
  and understand where exactly $\sqrt{\log n}\to\log n/\log\log n$ is "lost" in the constraint technique.

### 16.97. Exploratory step: treewidth gives tight depthvssize for Tseitin in boundeddepth Frege (Galesi-Itsykson-Riazanov-Sofronova 2019)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected undirected graph on $n$ vertices, $t=\mathrm{tw}(G)$, and $\mathrm{Tseitin}(G,f)$ is unsatisfiable.
  Then there exist constants $K,C>0$ such that for any $d\le K\log n/\log\log n - C$ any depth$d$ Fregerefutation
  has size $\ge 2^{t^{\Omega(1/d)}}$ (Galesi-Itsykson-Riazanov-Sofronova 2019, Thm. 18,
  `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`).
  Moreover, for all sufficiently large $d$ there is a depth$d$ Fregerefutation of size $\le 2^{t^{O(1/d)}}\cdot\mathrm{poly}(|\mathrm{Tseitin}(G,f)|)$
  (ibid., Thm. 19).
- `Toy test:` if $\mathrm{tw}(G)=\Omega(n)$ (in particular, for boundeddegree expanders, as noted in the same work),
  then polynomialsize ($n^{O(1)}$) is possible only for $d=\Omega(\log n/\log\log n)$ (according to Thm. 18).
  At the same time upper Thm. 19 is written as $2^{t^{O(1/d)}}\\cdot\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)$ and is correct/informative for fixed $d$.
  If $d$ grows with $n$ (as in the "threshold" mode $d\\approx\\log n/\\log\\log n$), then you need to track the dependence on $d$ in big-O:
  explicit unpack via Claim 28 gives an estimate of $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ and certifies polynomialsize on grids/expanders
  only at depth $d=\\Theta(\\log n)$ (see Section 16.115-Section 16.121).
- `Status:` known fact (exact link + clarification about the increasing depth mode; updates the output for Q15).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if you need to connect it with the "search for evidence", extract Cor. 34 from the same work:
  bounded-depth Frege of size $S$  tree-like Resolution of size $2^{\mathrm{poly}(\log_2 S)}$.

### 16.98. Research step: boundeddepth Frege  treelike Resolution (quasipoly) for Tseitin (GIRS 2019, Cor. 34)

- `Lens:` Equivalence.
- `Statement:` For any unsatisfiable Tseitin-CNF $\mathrm{Tseitin}(G,f)$: if it has a proof of size $S$
  in bounded-depth Frege (in the sense of the article; "constant-depth Frege" is mentioned below), then it has a tree-like Resolution refutation
  size $\le 2^{\mathrm{poly}(\log_2 S)}$ (Galesi-Itsykson-Riazanov-Sofronova 2019, Cor. 34,
  `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`).
- `Proof (sketch from Section 5 of the same work):` there they use (i) an upper bound on the treelike Resolution in terms of width:
  by Section 16.99 (Beame-Beck-Impagliazzo 2016, Lemma 61) we have $\mathrm{size}_{\mathrm{TL\text{-}Res}}\le n^{O(\mathrm{cw}(G))}$;
  according to Section 16.100-16.101 (and the definition of $w(G):=W(T(G,\\varphi)\\vdash\\bot)-1$) we obtain $\mathrm{cw}(G)\le w(G)+2$, which means
  $\mathrm{size}_{\mathrm{TL\text{-}Res}}(T(G,\\varphi))\le n^{O(w(G))}=2^{O(\mathrm{tw}(G)\,\Delta(G)\,\log_2 n)}$
  (Harvey-Wood 2014, (2); see Section 16.102); (ii) lower bound from the main theorem for boundeddepth Frege: $S\ge 2^{\mathrm{tw}(G)^{\varepsilon}}$
  for some constant $\varepsilon>0$ (depth is fixed); (iii) $S\ge|\mathrm{Tseitin}(G,f)|\ge 2^{\Delta(G)-1}$ and $S\ge n$ are trivial.
  Hence $\mathrm{tw}(G)\le (\log_2 S)^{1/\varepsilon}$, $\Delta(G)\le O(\log_2 S)$ and $\log_2 n\le O(\log_2 S)$, and substitution in (i)
  gives $2^{O((\log_2 S)^{1/\varepsilon+2})}=2^{\mathrm{poly}(\log_2 S)}$.
- `Toy test:` if $S=n^{O(1)}$, then we obtain a tree-like Resolution of size $\le 2^{\mathrm{poly}(\log_2 n)}=n^{\mathrm{polylog}\,n}$ (quasi-poly).
- `Status:` known fact (exact formulation + minimal conclusion "where does $2^{\mathrm{poly}(\log_2 S)}$ come from).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary, move the chain Section 16.99-16.102 (definition of $w(G)$ and $n^{O(w(G))}$) to the main text
  next to the wording Cor. 34, so as not to refer to "see. discussion".

### 16.99. Exploratory step: treelike Resolutionupper bound for Tseitin via carving width (Beame-Beck-Impagliazzo 2016)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a graph on $n$ vertices with carving width $W$ (Definition 58). Then the corresponding
  The Tseitin tautology $\tau(G)$ has a tree-like resolution representation of rank $\le W\log_{3/2} n$; in particular,
  there is a tree-like resolution-refutation of size $\le n^{O(W)}$ and clause space $\le W\log_{3/2} n+1$
  (Beame–Beck–Impagliazzo 2016, Lemma 61,
  `../../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`).
- `Toy test:` for $W=O(1)$ we obtain polynomialsize treelike resolution for $\tau(G)$ (and tree depth $O(\log n)$);
  for each recursive cut according to the (1/3,2/3)-lemma, the rank increases by $\le W$, and the recursion height is equal to $\log_{3/2} n$.
- `Status:` known fact (exact link; covers "where exactly" tree-like upper bound comes from, i.e. component [3] in GIRS'19 Cor. 34).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` link the parameter $W$ (carving width) with $w(G)$ from GIRS'19 (minimum resolutionwidth for Tseitin)
  and write down the minimal chain of inequalities needed for $n^{O(w(G))}$.

### 16.100. Research step: carving width $\le \mathrm{tw}(L(G))+1$ (and therefore $n^{O(W)}=n^{O(w(G))}$)

- `Lens:` Equivalence.
- `Statement:` For any graph $G$, $\mathrm{cw}(G)\le \mathrm{tw}(L(G))+1$ holds, where $\mathrm{cw}$ is the carving width,
  and $L(G)$ is a line graph. Therefore, using the formula for Tseitinwidth
  $w(G)=\max\{\Delta(G),\mathrm{tw}(L(G))\}-1$ (Galesi–Talebanfard–Torán 2018, Cor. 8+16,
  `../../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`), we obtain $\mathrm{cw}(G)\le w(G)+2$, and the upper bound
  from Section 16.99 of the form $n^{O(\mathrm{cw}(G))}$ is equivalent to $n^{O(w(G))}$.
- `Proof:` Let $(T,\{B_t\})$ be a tree decomposition of the graph $L(G)$ of width $k=\mathrm{tw}(L(G))$,
  those. $|B_t|\le k+1$.
  For a vertex $v\in V(G)$, the set of edges $E(v)$ forms a clique in $L(G)$, which means (by the Helly property for subtrees in $T$)
  there is a node $t_v\in V(T)$ such that $E(v)\subseteq B_{t_v}$.
  Add to $T$ a sheet $\ell_v$ with an edge $\ell_v t_v$ and set $\chi(\ell_v)=v$; we get a carving tree
  (if necessary, it can be made into a binary standard "split" of nodes with copies of the same bag - the width does not increase).
  Consider the edge $xy$ of this tree and the induced cut $V(G)=A\sqcup B$ along the leaves.
  If $xy=\ell_v t_v$, then $|E(A,B)|=\deg(v)\le |B_{t_v}|\le k+1$.
  Otherwise, $xy$ connects two bag nodes: if $uv\in E(A,B)$, then in $L(G)$ the vertex $e=\{u,v\}$ lies in both $B_{t_u}$ and $B_{t_v}$,
  this means its set of appearances in tree decomposition is a connected subtree containing the path $t_u\leadsto t_v$ and, in particular, the edge $xy$.
  Therefore, $e\in B_x\cap B_y$, that is, $E(A,B)\subseteq B_x\cap B_y$ and $|E(A,B)|\le |B_x\cap B_y|\le k+1$.
  This means that the width of the constructed carving decomposition is $\le k+1$, i.e. $\mathrm{cw}(G)\le \mathrm{tw}(L(G))+1$.
- `Toy test:` for cycle $C_n$: $\mathrm{tw}(L(C_n))=2$, so $\mathrm{cw}(C_n)\le 3$ (in fact $\mathrm{cw}(C_n)=2$);
  for the star $K_{1,n}$: $\mathrm{tw}(L)=n-1$ and $\mathrm{cw}(K_{1,n})=n=\mathrm{tw}(L)+1$.
- `Status:` proven.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` now that the original source $w(G)=\max\{\Delta(G),\mathrm{tw}(L(G))\}-1$ is fixed (16.101),
  update chain in Section 16.98/Cor. 34: tree-like upper bound $n^{O(\mathrm{cw}(G))}$ can be replaced by $n^{O(w(G))}$ without reference holes.

### 16.101. Exploratory step: exact reference to $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ for Tseitinwidth

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a connected graph and $\\varphi$ be an odd marking, so Tseitin-CNF $T(G,\\varphi)$ is unsatisfiable.
  Then the minimum width of the resolution refutation satisfies
  $$W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\},$$
  where $\\Delta(G)$ is the maximum degree, $L(G)$ is the line graph. In GIRS'19 notation (Cor. 33),
  where $w(G)=W(T(G,\\varphi)\\vdash\\bot)-1$, we get
  $$w(G)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1.$$
- `Proof (by source):` Galesi-Talebanfard-Toran (2018) prove (i) Cor. 8:
  $W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{ec}(G)-1\\}$, and (ii) Cor. 16:
  $\\mathrm{ec}(G)=\\mathrm{tw}(L(G))+1$; substitution gives the required formula.
  See `../../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`.
- `Toy test:` for the star $K_{1,n}$ we have $\\Delta=n$ and $L(G)=K_n$ with $\\mathrm{tw}(K_n)=n-1$,
  means $W=\\max\\{n,n-1\\}=n$ (and $w=n-1$), which is consistent with the fact that initial clauses have width $n$.
  For cycle $C_n$: $\\Delta=2$ and $L(C_n)=C_n$ with $\\mathrm{tw}=2$, so $W=2$ (and $w=1$).
- `Status:` known fact (exact link; closes Q19).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` compare this treewidth formula with an alternative parameterization of Tseitin-width via branch-width
  from Alekhnovich-Razborov (2011) (possible replacement of $\\mathrm{tw}(L(G))$ with an equivalent "width").

### 16.102. Research step: $n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log_2 n)}$ (via estimates on $\\mathrm{tw}(L(G))$)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected graph on $n$ vertices and $\\varphi$ an odd labeling, so that Tseitin-CNF $T(G,\\varphi)$ is unsatisfiable.
  Let us denote $w(G):=W(T(G,\\varphi)\\vdash\\bot)-1$. Then
  $$n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log_2 n)}.$$
- `Proof:` By Section 16.101 we have $w(G)+1=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}$.
  According to Harvey-Wood (2014), inequality (2), $\\mathrm{tw}(L(G))\\le (\\mathrm{tw}(G)+1)\\Delta(G)-1$
  (`../../resources/downloads/harvey_wood_2014_treewidth_line_graphs.pdf`).
  Therefore $w(G)=O(\\mathrm{tw}(G)\\,\\Delta(G))$ and therefore
  $$n^{O(w(G))}=2^{O(w(G)\\log_2 n)}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log_2 n)}.$$
- `Toy test:` for the star $K_{1,n}$: $\\mathrm{tw}(G)=1$, $\\Delta(G)=n$, and the formula gives $2^{O(n\\log_2 n)}$, which agrees with $n^{O(w)}$ for $w=n-1$ (16.101).
- `Status:` proven (inference from known facts).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` update the language in Section 16.98/Cor. 34 so that $2^{O(\\mathrm{tw}(G)\\Delta(G)\\log n)}$ appears with an explicit link (close Q20).

### 16.103. Research step: Tseitinwidth through branchwidth of a hypergraph (Alekhnovich-Razborov 2011)

- `Lens:` Equivalence.
- `Statement:` For any connected graph $G$ and odd labeling $\sigma$ (so TseitinCNF $T(G,\sigma)$ is unsatisfiable)
  branchwidth $\\mathrm{wb}(T(G,\\sigma))$ of its "subject hypergraph" $H_{T(G,\\sigma)}$ satisfies
  $$\\mathrm{wb}(T(G,\\sigma))=\\Theta\\bigl(W(T(G,\\sigma)\\vdash\\bot)\\bigr),$$
  where $W(F\\vdash\\bot)$ is the minimum resolutionwidth (Alekhnovich-Razborov 2011, Thm. 2.12,
  `../../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`).
  Moreover, $H_{T(G,\\sigma)}$ coincides with the dual hypergraph $G^*$ (with repetitions of hyperedges), see Remark 2.11 there.
  Hyperedge repetitions do not change $\\mathrm{wb}$ for this case, see Section 16.106.
  In particular, together with the exact formula of Section 16.101 we obtain the comparison
  $$\\mathrm{wb}(T(G,\\sigma))=\\Theta\\bigl(\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}\\bigr).$$
- `Toy test:` for $K_{1,n}$ we have $W=n$ (16.101) and $\\mathrm{wb}=\\Theta(n)$ by Thm. 2.12; for $C_n$ we have $W=2$ and $\\mathrm{wb}=\\Theta(1)$.
- `Status:` known fact (exact link; closes Q21).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if you need to use without $\\Theta(\\cdot)$, extract Thm from the proof. 2.12 explicit constants in both directions (see Q22).

### 16.104. Exploratory step: explicit constants in $\\mathrm{wb}(T(G,\\sigma))=\\Theta(W(T(G,\\sigma)\\vdash\\bot))$

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a connected graph and $T(G,\\sigma)$ the corresponding unsatisfiable Tseitin-CNF. Let's denote
  $$W:=W(T(G,\\sigma)\\vdash\\bot),\\qquad B:=\\mathrm{wb}(T(G,\\sigma)),$$
  where $W$ is the minimum resolution-width, $B$ is the branch-width of the underlying hypergraph (AR'11 Remark 2.11). Then the explicit inequalities are satisfied
  $$\\frac{1}{8}B\\ \\le\\ W\\ \\le\\ 2B.$$
- `Proof (from AR'11, Section 4):`
  1) (Gaussian width) Let $w_g(G,\\sigma)$ be the minimum width of the Gaussian representation (Def. 4.2). Then according to Prop. 4.3
     $$\\tfrac12 W\\le w_g(G,\\sigma)\\le W.$$
  2) (Branch-width vs Gaussian width) The proof of Lemma 4.4 shows that $B\\ge w_g(G,\\sigma)$ (tree-like restriction),
     and "algorithm Figure 3.1 + obstacle argument" gives $B\\le 8\\,w_g(G,\\sigma)$ (the estimate from the proof of Lemma 3.1 is repeated).
     Therefore $w_g(G,\\sigma)\\le B\\le 8w_g(G,\\sigma)$.
  3) Combining 1)-2), we obtain $W\\le 2w_g\\le 2B$ and $B\\le 8w_g\\le 8W$, i.e. $B/8\\le W\\le 2B$.
  Links: `../../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- `Toy test:` for $K_{1,n}$ (16.101) $W=n$ and $B\\ge r(H)=n$, so $B/8\\le W\\le 2B$ holds; for $C_n$ we have $W=2$ and $B=\\Theta(1)$.
- `Status:` proven (from explicit constants in AR'11).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if you want to remove the constant 8, check whether in Lemma 4.4 you can get $B\\le c\\,w_g$ with a smaller $c$ (or equality) for $G^*$.

### 16.105. Exploratory step: $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$ (branchwidth of the dual hypergraph = carving width)

- `Lens:` Equivalence.
- `Statement:` Let $G=(V,E)$ be a connected graph, and $G^*$ its dual hypergraph with the set of vertices $E$ and hyperedges
  $E(v)=\\{e\\in E: e\\text{ incident }v\\}$ for $v\\in V$. Then
  $$\\mathrm{wb}(G^*)=\\mathrm{cw}(G),$$
  where $\\mathrm{wb}$ is the branch-width of the hypergraph (AR'11, Def. 2.1), and $\\mathrm{cw}$ is the carving width of the graph $G$ (as in Section 16.99-16.100).
- `Proof:` In the branch-decomposition of the hypergraph $G^*$, the leaves correspond to the hyperedges $E(v)$, that is, the vertices $v\\in V$.
  Let $(T,\\theta)$ be a branch-decomposition of $G^*$. Let us define the marking of leaves $\\chi: \\mathrm{Leaves}(T)\\to V$ as $\\chi(\\theta(E(v)))=v$.
  Consider any nonzero node $t$ of the tree (i.e., $t\\ne\\mathrm{root}$) and let $S_t\\subseteq V$ be the set of vertices whose leaves lie in the subtree $t$.
  Then, by definition of AR'11 (Def. 2.1) we have
  $$\\mathrm{Cut}(t)=\\Bigl(\\bigcup_{v\\in S_t}E(v)\\Bigr)\\cap\\Bigl(\\bigcup_{v\\notin S_t}E(v)\\Bigr)=\\delta_G(S_t),$$
  that is, the set of edges of the graph $G$ intersecting the cut $S_t\\sqcup(V\\setminus S_t)$.
  Therefore, the order of node $t$ is $|\\delta_G(S_t)|$.
  Noting that each node $t\\ne\\mathrm{root}$ corresponds to an edge $t\\text{--parent}(t)$, we obtain a carving decomposition of $G$ on the same tree $T$
  (ignoring orientation): the cut width at edge $t\\text{--parent}(t)$ is equal to $|\\delta_G(S_t)|=|\\mathrm{Cut}(t)|$.
  Hence $\\mathrm{cw}(G)\\le \\mathrm{wb}(G^*)$.

  In the opposite direction: from any carving-decomposition $(T,\\chi)$ of the graph $G$ (leaves are marked by vertices) we construct a branch-decomposition $G^*$,
  putting $\\theta(E(v)):=\\chi^{-1}(v)$. For node $t\\ne\\mathrm{root}$, the set of $S_t$ leaves in the subtree again defines the cut of vertices,
  and the same formula shows $\\mathrm{Cut}(t)=\\delta_G(S_t)$. This means that the widths coincide on each corresponding cut, and
  $\\mathrm{wb}(G^*)\\le \\mathrm{cw}(G)$.
  Jointly: $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$.
- `Toy test:` for a star $K_{1,n}$: $\\mathrm{cw}(K_{1,n})=n$ (any cut separating the center from the leaf cuts $n$ edges) and $G^*$ has hyperedges
  sizes $n$ and $1$, so $\\mathrm{wb}(G^*)=n$; for cycle $C_n$: $\\mathrm{cw}(C_n)=2$ and $\\mathrm{wb}(C_n^*)=2$.
- `Status:` proven (closes Q23).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` use $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$ to rewrite AR parameters for Tseitin (Remark 2.11) directly via carving width,
  and compare with the treewidth formula Section 16.101.

### 16.106. Exploratory step: repetitions of hyperedges in $G^*$ do not change $\\mathrm{wb}$ (to apply Remark 2.11)

- `Lens:` Equivalence.
- `Statement:` Let $G=(V,E)$ be a connected graph without loops. Let us denote the dual hypergraph
  $$G^* := \\bigl(E,\\ \\{E(v): v\\in V\\}\\bigr),\\qquad E(v):=\\{e\\in E: e\\text{ incident }v\\}.$$
  Let $\\widetilde G^*$ be a multihypergraph on the same vertex set $E$ in which each hyperedge $E(v)$ is repeated $m_v\\ge 1$ times.
  Then
  $$\\mathrm{wb}(\\widetilde G^*)=\\mathrm{wb}(G^*).$$
  In particular, by AR'11 Remark 2.11 the underlying hypergraph TseitinCNF $T(G,\\sigma)$ is exactly $\\widetilde G^*$ for $m_v=2^{\\deg_G(v)-1}$, and therefore
  $$\\mathrm{wb}(T(G,\\sigma))=\\mathrm{wb}(H_{T(G,\\sigma)})=\\mathrm{wb}(G^*).$$
- `Proof:`
  1) (**Monotonicity in removing hyperedges.**) If $H'=(V,E')$ is obtained from $H=(V,E)$ by removing hyperedges (submultiset $E'\\subseteq E$),
     then $\\mathrm{wb}(H')\\le \\mathrm{wb}(H)$.
     Indeed, let us take branchdecomposition $(T,\\theta)$ for $H$.
     Consider the minimal subtree $T'\\subseteq T$ spanned by the leaves $\\theta(E')$,
     and suppress all vertices of degree 2 in it (receiving a binary rooted tree again) - this gives branch-decomposition for $H'$.
     For each node $t$ in the new tree, the sets of descendant hyperedges on both sides of the cut are subsets of the corresponding sets in $T$,
     therefore $V(t)$ and $V^\\perp(t)$ only decrease, which means $|\\mathrm{Cut}(t)|=|V(t)\\cap V^\\perp(t)|$ does not increase.
  2) (**Lower bound $\\mathrm{wb}(G^*)\\ge \\Delta(G)$.**) For any $v\\in V$ and any branch-decomposition $(T,\\theta)$ of the hypergraph $G^*$
     the sheet $t_v:=\\theta(E(v))$ has
     $$\\mathrm{Cut}(t_v)=E(v)\\cap\\bigcup_{u\\ne v}E(u)=E(v),$$
     since every edge $e\\in E(v)$ is also incident to some $u\\ne v$ (no loops).
     Therefore, the leaf order is $|E(v)|=\\deg_G(v)$, and therefore $\\mathrm{wb}(G^*)\\ge \\max_v \\deg_G(v)=\\Delta(G)$.
  3) (**Construct a decomposition for $\\widetilde G^*$.**) Let $(T,\\theta)$ be the optimal branch-decomposition $G^*$ of width $w:=\\mathrm{wb}(G^*)$.
     For each $v\\in V$ we replace the leaf $\\theta(E(v))$ with a binary subtree with $m_v$ leaves,
     copies of the hyperedge $E(v)$ labeled with $m_v$ (the root of the subtree takes the place of the old leaf).
     We obtain branchdecomposition $(\\widetilde T,\\widetilde\\theta)$ of the hypergraph $\\widetilde G^*$.
     For nodes outside the added subtrees, the cuts do not change: each side now has either zero or all copies of $E(v)$,
     and the union over copies is equal to $E(v)$.
     For a node $t$ inside the subtree corresponding to $v$, there is at least one copy of $E(v)$ on both sides of the cut,
     therefore $V(t)=V^\\perp(t)=E(v)$ and $|\\mathrm{Cut}(t)|=|E(v)|=\\deg_G(v)\\le \\Delta(G)\\le w$ (by item 2).
     Consequently, the width of $(\\widetilde T,\\widetilde\\theta)$ does not exceed $w$, that is, $\\mathrm{wb}(\\widetilde G^*)\\le \\mathrm{wb}(G^*)$.
  4) In the opposite direction, $G^*$ is obtained from $\\widetilde G^*$ by removing copies of hyperedges, therefore, by item 1
     $\\mathrm{wb}(G^*)\\le \\mathrm{wb}(\\widetilde G^*)$.
     Together: $\\mathrm{wb}(\\widetilde G^*)=\\mathrm{wb}(G^*)$.
- `Toy test:`
  1) For $K_{1,n}$, the hyperedge $E(\\text{center})$ is repeated $2^{n-1}$ times, but both values of $\\mathrm{wb}(G^*)$ and $\\mathrm{wb}(\\widetilde G^*)$ are equal to $n$ (see Section 16.105).
  2) (Why the statement cannot be generalized.) If $H$ has two disjoint hyperedges $A,B$ of size $r$, then $\\mathrm{wb}(H)=0$,
     but when adding a second copy of $A$ we get $\\mathrm{wb}\\ge |A|=r$ (leaf corresponding to one copy).
- `Status:` proven (closes Q24).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` in the main text (or the final remark for Section 16.103-16.105), you can reduce the AR'11 chain to a short formula
  $W(T(G,\\sigma)\\vdash\\bot)=\\Theta(\\mathrm{cw}(G))$ via $\\mathrm{wb}(T)=\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$.

### 16.107. Exploratory step: $W(T(G,\\sigma)\\vdash\\bot)=\\Theta(\\mathrm{cw}(G))$ (explicit constants)

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a connected graph without loops, and let $\\sigma:V(G)\\to\\{0,1\\}$ be such that Tseitin-CNF $T(G,\\sigma)$ is unsatisfiable.
  Let $W:=W(T(G,\\sigma)\\vdash\\bot)$ denote the minimum resolutionwidth. Then
  $$\\frac{1}{8}\\,\\mathrm{cw}(G)\\ \\le\\ W\\ \\le\\ 2\\,\\mathrm{cw}(G).$$
  In particular, $W(T(G,\\sigma)\\vdash\\bot)=\\Theta(\\mathrm{cw}(G))$.
- `Proof:` By Section 16.104 we have $\\tfrac18\\,\\mathrm{wb}(H_{T(G,\\sigma)})\\le W\\le 2\\,\\mathrm{wb}(H_{T(G,\\sigma)})$ (AR'11, Thm. 2.12 + Section 4).
  By AR'11 Remark 2.11, $H_{T(G,\\sigma)}$ is a multi-$G^*$, and by Section 16.106, repetitions of hyperedges do not change $\\mathrm{wb}$, which means
  $\\mathrm{wb}(H_{T(G,\\sigma)})=\\mathrm{wb}(G^*)$.
  By Section 16.105, $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$. Substitution gives the required inequality.
- `Toy test:` for $K_{1,n}$ we have $\\mathrm{cw}(K_{1,n})=n$ and $W=n$ (by formula Section 16.101); for the cycle $C_n$ we have $\\mathrm{cw}(C_n)=2$ and $W=2$.
- `Status:` proven (closes Q25).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check "planar graphs with bounded degree of faces  bounded cyclicity $\\ell(G)$" from AR'11 (paragraph after Thm. 2.16),
  to understand when $W\\le \\ell(G)^{O(1)}\\log S$ actually gives automatability.

### 16.108. Research step: bounded face degree (planar)  bounded cyclicity $\\ell(G)$ (clarification of AR'11 remark after Thm. 2.16)

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a connected planar graph that admits a plane embedding in which each face has degree $\\le d$
  (the length of the boundary tour, counting multiplicities), and let $G$ be 2-edge-connected (no bridges).
  Then cyclicity $\\ell(G)$ from AR'11 Def. 2.14 satisfies
  $$\\ell(G)\\le \\max\\{d,2\\}.$$
- `Proof:`
  Consider a fixed flat embedding. For each face $f$ we take its boundary closed walk $W_f$ of length $\\deg(f)\\le d$.
  Since $G$ has no bridges, each edge is incident to two different faces and therefore occurs exactly once in each of the two traversals
  (equivalent to: an edge enters the boundary of the same face twice if and only if it is a bridge).
  Therefore, $W_f$ is a closed traversal without edge repetitions.

  Any such traversal can be decomposed into pairwise edge-disjoint simple cycles (induction on length: if a vertex is repeated in $W_f$,
  then we cut the traversal at the repetition point into two shorter closed traversals; otherwise it's a simple loop).
  In particular, all cycles in the decomposition have length $\\le |W_f|\\le d$, and each edge lying on the boundary of $f$ belongs to exactly one cycle from this decomposition.

  Let's take the union of cycles along all faces. Then each edge $e$ belongs to exactly two faces, which means it falls into at most two cycles (one "from the side" of each face),
  and all cycles have length $\\le d$. This is the coverage of edges by cycles, satisfying the definition of cyclicity with the parameter $\\max\\{d,2\\}$.
- `Toy test:` a triangle with a "tail" (a suspended edge-bridge) has an embedding with $d=5$, but covering the edges with cycles is impossible (the bridge does not lie in any cycle),
  so the "no bridges" condition is really necessary.
- `Status:` proven (closes Q26; explains AR'11 remark after Thm. 2.16,
  `../../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if you want to use Theorem 2.15 quantitatively, extract the explicit power in $\\ell(G)^{O(1)}$ from the AR'11 proof (instead of $O(1)$).

### 16.109. Research Step: Explicit Degree in AR'11 Thm. 2.15 (comes out to $\\ell^7$)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected graph for which cyclicity $\\ell(G)<\\infty$ and $\\sigma$ be an odd labeling (so $T(G,\\sigma)$ is unsatisfiable).
  Let $\\ell:=\\ell(G)$, $W:=W(T(G,\\sigma)\\vdash\\bot)$ denote the minimum resolution-width and $S:=S(T(G,\\sigma)\\vdash\\bot)$ the minimum size of the resolution refutation.
  Then there is an absolute constant $C>0$ such that
  $$W\\le C\\,\\ell^7\\,\\log S.$$
  In particular, this makes explicit the degree in AR'11 notation $W\\le \\ell(G)^{O(1)}\\log S$.
- `Proof:` In evidence AR'11 Thm. 2.15 (section 5) two estimates were obtained:
  (i) by (5.4) $W(T(G,\\sigma)\\vdash\\bot)\\le O(\\ell\\cdot W(T(G,\\sigma)|\\rho\\vdash\\bot))$ for the constructed random restriction $\\rho$;
  (ii) by (5.6) with "overwhelming probability" $W(T(G,\\sigma)|\\rho\\vdash\\bot)\\le O(\\ell^6\\log S)$ is satisfied.
  Multiplying, we get $W\\le O(\\ell^7\\log S)$.
  Link: `../../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`, Section 5 (equations (5.4) and (5.6)).
- `Toy test:` if $\\ell$ is bounded by an absolute constant, then $W=O(\\log S)$ (smoothness).
  Together with Section 16.108: for 2-edge-connected planar graphs with $\\max\\deg(\\text{face})\\le d$ we obtain $W\\le O(d^7\\log S)$.
- `Status:` known fact (explicit degree extraction; closes Q27).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` similarly try to make the dependence explicit in AR'11 Thm. 2.17 (quasi-smoothness via $\\tilde\\ell(G)$).

### 16.110. Exploratory step: explicit constant in Thm. 2.17 (you can take $c=6$)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected graph, $\\tilde\\ell:=\\tilde\\ell(G)<\\infty$ be an AR'11 parameter (after Thm. 2.16),
  $\\sigma$ - odd marking (so $T(G,\\sigma)$ is impossible), $W:=W(T(G,\\sigma)\\vdash\\bot)$ - minimum resolutionwidth,
  $S:=S(T(G,\\sigma)\\vdash\\bot)$ is the minimum size of a resolution refutation. Then for some absolute constant $C>0$ it is true
  $$W\\le (C\\,\\tilde\\ell\\,\\log S)^{6\\tilde\\ell^2}.$$
  This makes the dependence in AR'11 Thm clear. 2.17: $W\\le (\\tilde\\ell\\log S)^{O(\\tilde\\ell^2)}$.
- `Proof:` In evidence AR'11 Thm. 2.17 (section 5) fix $\\ell:=\\tilde\\ell(G)$ and get:
  1) by (5.12) there exists (with probability $1-O(S^{-1})$) a constraint $\\rho$ such that
     $$W(T(G,\\sigma)|\\rho\\vdash\\bot)\\le w:=\\bigl(K\\ell^2\\log S\\bigr)^{\\ell}.$$
  2) by Claim 5.17, provided that $E_p$ is regular (Claim 5.16) from $W(T|\\rho)\\le w$ it follows
     $$\\mathrm{wb}(T(G,\\sigma)\\vdash\\bot)\\le w^2 + R,$$
     where $R$ is the number of "relevant edges" for some pair $(V_0,V_1)$ with $|V_0|,|V_1|\\le w$.
  3) We make the estimate of $R$ explicit: in the definition of $P_{V_0,V_1}$ all paths have length $\\le 2\\ell-1$, which means each set of edges in the family has size $\\le 2\\ell$.
     After the plucking procedure in $F_{V_0,V_1}$ there is no sunflower family of size $r$ among the minimal elements, where $r=C_0 w\\log n$ (see (5.15)), $n:=|V(G)|$.
     Therefore, by Erdos-Rado (Prop. 5.8) we obtain the explicit estimate
     $$|F_{V_0,V_1}|\\le (2\\ell)!\\,(r-1)^{2\\ell}\\le (2\\ell)!\\,r^{2\\ell},$$
     which means the number of relevant edges satisfies
     $$R\\le (2\\ell)\\,|F_{V_0,V_1}|\\le 2\\ell\\,(2\\ell)!\\,r^{2\\ell}.$$
  4) Substitution $r=C_0 w\\log n$ gives
     $$R\\le 2\\ell\\,(2\\ell)!\\,(C_0\\log n)^{2\\ell}\\,w^{2\\ell}.$$
     By Section 16.112 we have $S\\ge n$, which means $\\log n\\le \\log S$.
     Also $(2\\ell)!\\le (2\\ell)^{2\\ell}$, so
     $$2\\ell\\,(2\\ell)!\\,(C_0\\log n)^{2\\ell}\\le (C_1\\,\\ell\\,\\log S)^{4\\ell}.$$
     Hence,
     $$\\mathrm{wb}(T(G,\\sigma)\\vdash\\bot)\\le w^2 + (C_1\\ell\\log S)^{4\\ell}\\,w^{2\\ell}.$$
  5) Since $w=(K\\ell^2\\log S)^{\\ell}$, we have $w^{2\\ell}=(K\\ell^2\\log S)^{2\\ell^2}$, and the factor is $(C_1\\ell\\log S)^{4\\ell}$
     increases the degree by no more than $4\\ell\\le 4\\ell^2$.
     Therefore (absorbing constants and passing from branchwidth to width via AR'11 Thm. 2.12 + Remark 2.11 + Section 16.106) we get
     $$W\\le (C\\,\\ell\\,\\log S)^{6\\ell^2}.$$
- `Toy test:` if $\\ell=O(1)$, then $W\\le (\\log S)^{O(1)}$ (quasi-smoothness) is consistent with the AR'11 formulation.
- `Status:` proven (rough explicit constant; closes Q28).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary, improve the rough constant 6 (refine the estimates by $|F_{V_0,V_1}|$ / relevant edges).

### 16.111. Research step: summary of AR'11 (Thm. 2.15/2.17/2.18) in "usable" form

- `Lens:` Equivalence.
- `Statement:` Let $G$ be a connected graph, $\\sigma$ an odd labeling (so Tseitin-CNF $T(G,\\sigma)$ is unsatisfiable), and
  $W:=W(T(G,\\sigma)\\vdash\\bot)$, $S:=S(T(G,\\sigma)\\vdash\\bot)$.
  Then:
  1) (**Smoothness via cyclicity.**) If $\\ell:=\\ell(G)$ is finite, then
     $$W\\le O(\\ell^7\\log S)$$
     (AR'11, (5.4)+(5.6); explicit degree written in Section 16.109).
     In particular, if $G$ is 2-edge-connected, planar, and $\\max\\deg(\\text{face})\\le d$, then $\\ell(G)\\le\\max\\{d,2\\}$ (Section 16.108) and therefore
     $$W\\le O(d^7\\log S).$$
  2) (**Quasi-smoothness via $\\tilde\\ell$.**) If $\\tilde\\ell:=\\tilde\\ell(G)$ is finite, then
     $$W\\le (C\\,\\tilde\\ell\\,\\log S)^{6\\tilde\\ell^2}$$
     (AR'11, Claim 5.17/(5.18); the explicit constant $6$ is written out in Section 16.110).
  3) (**No parameters.**) For any $G$ the following holds:
     $$W\\le O(\\log S + |V(G)|)$$
     (AR’11, Thm. 2.18).
- `Toy test:` for fixed $d$ in (1) we obtain $W=O(\\log S)$ (smoothness), and for fixed $\\tilde\\ell$ in (2) we obtain $W\\le (\\log S)^{O(1)}$ (quasi-smoothness).
- `Status:` proven (summary; closes Q29).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary, transfer this summary to the main text (without dragging evidence) as 3-6 lines with reference to AR'11 and Section 16.108-16.110.

### 16.112. Exploratory step: for Tseitin $S(T(G,\\sigma)\\vdash\\bot)\\ge |V(G)|$ (and therefore $\\log n\\le\\log S$)

- `Lens:` Invariant.
- `Statement:` Let $G$ be a connected graph without loops, $\\sigma:V(G)\\to\\{0,1\\}$ is odd (so Tseitin-CNF $T(G,\\sigma)$ is unsatisfiable).
  For a vertex $v\\in V(G)$, let $B_v$ denote the set of clauses in the block $\\mathrm{PARITY}_{v,\\sigma(v)}$ (see AR'11, (2.9)).
  Then CNF $T(G,\\sigma)\\setminus B_v$ is satisfiable. In particular, any resolution refutation $T(G,\\sigma)$ must use
  at least one initial clause from each block $B_v$, and therefore
  $$S(T(G,\\sigma)\\vdash\\bot)\\ge |V(G)|.$$
- `Proof:`
  1) (**Satisfiability after removing one block.**) Fix a vertex $r$ and construct a satisfying assignment for all vertices $v\\ne r$.
     Take a spanning tree $T$ of a graph $G$ with root $r$. Let us set $x_e:=0$ for all edges $e\\notin E(T)$.
     Let's go around the vertices of $T$ from bottom to top. For each $v\\ne r$, let $p(v)$ be the parent, $e_v:=(v,p(v))$ be the edge to the parent.
     When the values of $x_f$ are already given for all edges $f$ incident to $v$, except $e_v$, we set
     $$x_{e_v}:=\\sigma(v)\\oplus \\bigoplus_{f\\ni v,\\ f\\ne e_v} x_f.$$
     Then the vertex $v$ satisfies the required equation $\\bigoplus_{f\\ni v}x_f=\\sigma(v)$.
     This means that the assignment satisfies all XOR constraints for $v\\ne r$ and, therefore, satisfies all clauses from the blocks $B_v$ for $v\\ne r$.
     Since the block $B_r$ has been removed, we obtain the satisfiability of $T(G,\\sigma)\\setminus B_r$.
  2) (**Hence the lower bound on the size.**) If the resolution refutation $\\pi$ does not use any original clause from the block $B_v$,
     then it is a resolution refutation of a satisfiable CNF $T(G,\\sigma)\\setminus B_v$, which is impossible due to the correctness of the resolution.
     Consequently, $\\pi$ uses at least one initial clause from each block, and the number of clauses in $\\pi$ is at least $|V(G)|$,
     that is, $S(T(G,\\sigma)\\vdash\\bot)\\ge |V(G)|$.
- `Toy test:` for a cycle $C_3$ with odd $\\sigma$ (exactly one vertex with charge 1), removing the block of this vertex makes a system of two XOR equations
  joint; the tree structure above clearly has a solution.
- `Status:` proven (closes Q30).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` use as a substitution $\\log|V(G)|\\le\\log S$ in places where $n$ appears inside $\\log$ (for example, in the estimates from AR'11 Section 5).

### 16.113. Research step: Frege"line replacement" by equivalence $A\\leftrightarrow A'$

- `Lens:` Compression/canonization.
- `Statement:` Let $\\Gamma$ be a set of formulas, and let the Frege derivation from $\\Gamma$ already yield formula $A$.
  If there is also a Frege derivation (without hypotheses) of the tautology $A\\leftrightarrow A'$, then $A'$ is deduced from $\\Gamma$.
  Moreover, $A'$ can be inserted into the output immediately after $A$ with $O(1)$ additional lines (plus the output of $A\\leftrightarrow A'$).
- `Proof:` We write $A\\leftrightarrow A'$ as $(A\\to A')\\wedge(A'\\to A)$.
  Any Frege system has short (constant) tautology outputs
  $((X\\wedge Y)\\to X)$ and $((X\\wedge Y)\\to Y)$.
  Applying modus ponens to the string $(A\\to A')\\wedge(A'\\to A)$, we get the string $A\\to A'$,
  and then modus ponens to the strings $A$ and $A\\to A'$ gives $A'$.
  (Similarly, $A$ is derived from $A'$ and $A\\leftrightarrow A'$.)
- `Blow-up rating:` one line replacement adds a constant number of lines beyond the equivalence output of $A\\leftrightarrow A'$,
  those. if $|\\pi|$ is the length of the original output and $E$ is the total length of the added equivalence outputs, then the new output has length $O(|\\pi|+E)$.
- `Toy test:` for $A=(p\\vee q)\\vee r$ and $A'=p\\vee(q\\vee r)$: from $A$ and the associativity of $\\vee$ (as $A\\leftrightarrow A'$) we derive $A'$.
- `Status:` proven (closes Q32).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary for a strict "logdepth" interpretation, record (with a link) what the selected balancing scheme gives
  polynomial Frege-derivation of the equivalence $A\\leftrightarrow A'$ for each line (otherwise, use the Buss'97 translation from Section 16.95).

### 16.114. Exploratory step: Spira balancing produces p-dimensional Frege-proofs $A\\leftrightarrow A'$

- `Lens:` Equivalence.
- `Statement:` There is a standard Spira scheme for balancing formulas $A\\mapsto A'$ of depth $O(\\log|A|)$ and size $\\mathrm{poly}(|A|)$, for which
  tautologies $A\\leftrightarrow A'$ have polynomial Frege-proofs. Therefore, argument 16.94 "balance each line" can be
  conduct strictly through Section 16.113.
- `Rationale/link:` in Buss (1997), Proof (Sketch) to Theorem 3 (p. 8),
  `../../resources/downloads/buss_1997_proof_complexity_intro.pdf`,
  It is explicitly noted that in the proof of p-simulation of Frege-systems by Rekhow/Spira
  «must prove that there are polynomial size proofs that the Spira translation of a conjunction $A\\wedge B$ is equivalent to the conjunction of the Spira translations of $A$ and $B$»,
  those. the correctness of the Spira translation (and, in particular, the equivalence of the original formula and its balancing) is verified inside Frege with a polynomial blow-up.
- `Toy test:` for $A=(p\\vee q)\\vee r$ and $A'=p\\vee(q\\vee r)$ the equivalence of $A\\leftrightarrow A'$ is derived from the associativity of $\\vee$ by a constant number of rows (see Section 16.113).
- `Status:` known fact (exact link; closes Q33).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` return to 16.93: either find a source with an explicit construction of the $O(\\log n)$depth Fregerefutation of Tseitin, or leave only the "Buss'97/Spira translation" as a strict upper bound on depth (16.95).

### 16.115. Research step: when the upper estimate of GIRS'19 Thm. 19 becomes polynomialsize?

- `Lens:` Trade-off.
- `Statement:` Let $t:=\\mathrm{tw}(G)$ and $\\Delta:=\\Delta(G)$.
  From the GIRS'19 Thm proof. 27/Claim 28 (Section 4.3; see also Section 16.119-Section 16.120) produces a **non-circular** explicit form of the upper bound:
  for any $d\\ge 1$ there is a boundeddepth Fregerefutation of the depth $O(d)$ and size
  $$\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)\\cdot 2^{\\,O\\bigl(d\\cdot X^{2/d}\\bigr)},\\qquad X:=\\Delta\\,\\mathrm{tpw}(G).$$
  Substituting $\\mathrm{tpw}(G)\\le 10\\Delta\\,t$ (GIRS'19 Thm. 26), we get
  $$\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)\\cdot 2^{\\,O\\bigl(d\\cdot (10\\Delta^2 t)^{2/d}\\bigr)}.$$
  In particular, polynomial-size is guaranteed already for $d=\\Theta(\\log(10\\Delta^2 t))$ (then $(10\\Delta^2 t)^{2/d}=2^{O(1)}$ and the exponent becomes $O(\\log t)$).
- `Proof:` according to Claim 28 (GIRS'19, p. 13), the size of the game tree is limited by $\\mathrm{poly}(|T|)$ and dominant terms of the form
  $2^{O(\\sum_{i=1}^d t_i)}$, where in the proof Thm. 27 choose $t_i=(\\Delta\\,\\mathrm{tpw}(G))^{2/d}$ for all $i$ (p. 14),
  so $\\sum_i t_i=d\\cdot X^{2/d}$. The constants in the Lemma 24/25 transition are fixed in Section 16.118, and therefore the final size
  has the form $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$. Substitution Thm. 26 gives the formula in terms of $t$.
- `Toy test:` if $d=\\Theta(\\log t)$ then $X^{2/d}=2^{O(1)}$ and the estimate becomes $2^{O(\\log t)}=\\mathrm{poly}(t)$.
- `Status:` proven (corrects 16.115: from GIRS'19 it **does not follow** polynomialsize for $d=\\Theta(\\log t/\\log\\log t)$ without additional ideas; see Section 16.120).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` for grid, rewrite the total in terms of $N$ and compare it with Hastad'20 Cor. 6.6 (see Section 16.116 and Section 16.120).

### 16.116. Exploratory step: Tseitin(Grid) -- polynomialsize depth threshold in terms of $N$

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a $n\\times n$ grid and $T:=\\mathrm{Tseitin}(G,f)$ be the corresponding Tseitin-CNF.
  Let us denote by $N$ the number of variables in $T$ (for standard coding $N=\\Theta(|E(G)|)=\\Theta(n^2)$).
  Then:
  1) (**Lower estimate.**) Any polynomialsize Fregerefutation in depth$d$ requires
     $$d\\ =\\ \\Omega\\!\\left(\\frac{\\log N}{\\log\\log N}\\right)$$
     (Hastad'20, Cor. 6.6; see Section 16.92).
  2) (**Upper estimate.**) Polynomialsize Fregerefutations exist at depth
     $$d\\ =\\ O(\\log N)$$
     (for example, from GIRS'19: polynomialsize already for $d=\\Theta(\\log\\mathrm{tw}(G))=\\Theta(\\log n)=\\Theta(\\log N)$; see Section 16.115 and Section 16.120).
  Therefore, the known zone for the minimum polynomialsize depth on the grid is:
  $$\\Omega\\!\\left(\\frac{\\log N}{\\log\\log N}\\right)\\ \\le\\ d_{\\mathrm{poly}}(N)\\ \\le\\ O(\\log N).$$
- `Proof:`
  1) (**Lower estimate.**) This is Cor. 6.6 from Hastad (2020) (see Section 16.92), rewritten as $N=\\Theta(n^2)$.
  2) (**Upper estimate.**) From Section 16.115 we have polynomialsize at depth $d=\\Theta(\\log(\\Delta^2\\mathrm{tw}(G)))$.
     For grid $\\Delta=4$ and $\\mathrm{tw}(G)=\\Theta(n)$, then $d=\\Theta(\\log n)=\\Theta(\\log N)$.
- `Toy test:` $N=n^2$ gives $\\log N=2\\log n$ and $\\log\\log N=\\log(\\log n+\\log 2)=\\log\\log n+O(1)$, so the scales
  $\\log n/\\log\\log n$ and $\\log N/\\log\\log N$ are the same in order.
- `Status:` proven (corrects 16.116: the order for $d_{\\mathrm{poly}}$ on the grid is **not** fixed; only $\\Omega(\\log N/\\log\\log N)$ and $O(\\log N)$ are known).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary for the "main text", replace "tight" with two-sided borders $\\Omega(\\log N/\\log\\log N)$ and $O(\\log N)$ (see. `docs/15_proof_complexity.md`).

### 16.117. Exploratory step: constants in the depth threshold for Tseitin(Grid) (Hastad'20 vs GIRS'19)

- `Lens:` Trade-off.
- `Statement:` For Tseitin(Grid$_{n,n}$) in boundeddepth Frege:
  1) (**Explicit lower constant.**) From Hastad (2020), Cor. 6.6 (see Section 16.92) it follows that polynomialsize is impossible when
     $$\\mathrm{depth}\\le \\frac{\\log n}{59\\,\\log\\log n}.$$
  2) (**Known upper.**) From Section 16.115 (based on GIRS'19 Thm. 27/26) it follows polynomialsize at depth $\\mathrm{depth}=O(\\log n)=O(\\log N)$.
  Therefore, a "constant" comparison of the form $1/59$ vs "$9c$" is invalid: the known upper bound for polynomialsize is on a different scale
  (between $\\Omega(\\log n/\\log\\log n)$ and $O(\\log n)$; see Section 16.116), and the task is to close this gap (or explain the barrier).
- `Proof:`
  1) Point (1) is exactly Cor. 6.6 from Hastad (2020), as recorded in Section 16.92.
  2) For grid $\\Delta=4$, $\\mathrm{tw}(G)=\\Theta(n)$, and according to Section 16.115, the polynomialsize is obtained at depth $\\Theta(\\log n)$.
- `Toy test:` for $d=\\alpha\\,\\log n/\\log\\log n$ from Section 16.115 we obtain the exponent $\\Theta(d\\cdot n^{2/d})=\\Theta\\bigl((\\log n)^{1+2/\\alpha}/\\log\\log n\\bigr)$,
  that is, it is guaranteed **not** polynomialsize; to make the exponent $O(\\log n)$, you need $d=\\Theta(\\log n)$.
- `Status:` proven (the scale has been clarified: the known upper for polynomialsize is $O(\\log n)$, and not $\\Theta(\\log n/\\log\\log n)$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find/construct upper on polynomialsize with depth $O(\\log n/\\log\\log n)$ (or an argument why the "compact parity" approach does not give this).

### 16.118. Research step: in GIRS'19 Lemma 24/25 you can take an explicit constant $c=21$

- `Lens:` Trade-off.
- `Statement:` In Galesi-Itsykson-Riazanov-Sofronova (2019) (GIRS'19) in Lemma 24 and Lemma 25
  (Section 4.2, "Summation of linear equations") you can choose the constant $c=21$:
  for any $d$ and any $p(t_1,\\dots,t_d)$refinement $U$ there is a derivation stated in Lemma 24 of size
  $\\le 21\\cdot|\\Phi_1(\\varnothing,U)|^6$, and therefore in Lemma 25 we can take the same constant (size $\\le 21k\\cdot|\\Phi_1(\\varnothing,U)|^6$).
- `Proof:` in the proof of Lemma 24 (GIRS'19, p. 10-11 in PDF numbering) the estimate was obtained
  $$\\text{size}\\ \\le\\ 2^{3t_1}\\,c\\,|\\Phi_1(\\varnothing,V^1)|^6\\ +\\ 20\\,|\\Phi_1(\\varnothing,U)|^6,$$
  and further the identity is used (ibid.)
  $$|\\Phi_1(\\varnothing,U)|=2^{t_1+1}t_1\\,|\\Phi_1(\\varnothing,V^1)|.$$
  Substituting, we get
  $$2^{3t_1}c|\\Phi_1(\\varnothing,V^1)|^6
    =c\\,\\frac{2^{3t_1}}{2^{6(t_1+1)}t_1^6}\\,|\\Phi_1(\\varnothing,U)|^6
    \\le \\frac{c}{512}\\,|\\Phi_1(\\varnothing,U)|^6,$$
  since $t_1\\ge 1$. Therefore, for $c=21$ we have
  $$\\frac{c}{512}+20<21,$$
  and the inductive step in Lemma 24 takes place with the same constant $c=21$ (the base $d=0$ gives a constant size and, moreover, fits into $21\\cdot|\\Phi_1(\\varnothing,U)|^6$).
  In Lemma 25 (p. 11), item (1) is $(k-1)$ of successive applications of Lemma 24 with composition by Lemma 2, so the size
  $\\le k\\cdot 21\\cdot|\\Phi_1(\\varnothing,U)|^6$.
- `Toy test:` for $t_1=1$, the worst factor in the first term is $2^{3}/2^{12}=1/512$, and there is still a margin of $21-20=1$.
- `Status:` proven (explicit constant; useful for Q39).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` unpack the remaining "there is $c$"/bigO in the upper estimate of GIRS'19 Thm. 19 (p. 14):
  now the only implicit constants sit in the transition from Claim 28/Theorem 27 to the form $2^{(10\\Delta^2\\mathrm{tw})^{c/d}}$.

### 16.119. Research step: in GIRS'19 Thm. 19 you can take the explicit constant $c=4$ (unpacking Claim 28 -> Thm. 27)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected graph, $T:=\\mathrm{Tseitin}(G,f)$ is unsatisfiable, and $d\\ge 1$.
  Let us denote $X:=\\Delta(G)\\,\\mathrm{tpw}(G)$. If $X^{1/d}\\ge \\max(2d,6)$, then in the GIRS'19 construction (Section 4.3)
  you can take the **explicit** constant $c=4$ in the exponent:
  there is a derivation of depth $3d+O(1)$ of size
  $$\\mathrm{poly}(|T|)\\cdot 2^{X^{4/d}}.$$
  Therefore, by Theorem 26 (GIRS'19) we can take the same constant $c=4$ in the form Thm. 19:
  $$\\mathrm{poly}(|T|)\\cdot 2^{(10\\Delta(G)^2\\mathrm{tw}(G))^{4/d}}.$$
- `Proof:` we fix explicit constants hidden in Claim 28 (GIRS'19, p. 13-14).
  Let $t_1=\\dots=t_d:=\\lceil X^{2/d}\\rceil$ and $Q$ - $(3,t_1,\\dots,t_d)$refinement, as in the proof of Thm. 27.
  Let $M:=|\\Phi^1(\\varnothing,Q)|$ (compact representation of parity).
  1) By Lemma 21 (GIRS'19) we have
     $$M\\le 48\\cdot\\prod_{i=1}^d 2^{t_i+1}t_i.$$
  2) In Claim 28, the largest sub-derivations are applications of Lemma 25; after fixing the constant $21$ in Lemma 24/25 (see Section 16.118)
     we obtain the size $\\le 21k\\,M^6$ (for $k\\le (\\Delta+1)\\mathrm{tpw}$), and the contribution of Lemma 22 ($\\le 4M^3$) and Lemma 4
     (for the transition of CNF parities to $\\Phi$ representations) is polynomial in $|T|$ and $M^6$.
     Therefore, the entire design of Thm. 27 gives an estimate of the form
     $$\\mathrm{size}\\le \\mathrm{poly}(|T|)\\cdot M^6.$$
  3) Since $t_i\\ge 1$, the factors of $t_i^6$ can be absorbed into $\\mathrm{poly}(|T|)$ (for our $t_i$ this is $\\le (2^dX^2)^{O(1)}$,
     and from $X^{1/d}\\ge 2d$ it follows $X\\ge 2^d$). From here
     $$M^6\\le \\mathrm{poly}(|T|)\\cdot 2^{6\\sum_{i=1}^d t_i}.$$
  4) For $t_i=\\lceil X^{2/d}\\rceil$ we have $\\sum_i t_i\\le d(X^{2/d}+1)\\le 2dX^{2/d}$.
     From the condition $X^{1/d}\\ge 2d$ we obtain $2dX^{2/d}\\le X^{3/d}$, which means
     $$6\\sum_i t_i\\le 6X^{3/d}.$$
     Finally, $X^{1/d}\\ge 6$ implies $6X^{3/d}\\le X^{4/d}$, that is, $M^6\\le \\mathrm{poly}(|T|)\\cdot 2^{X^{4/d}}$.
  Combining (2)-(4), we obtain the required explicit form for Thm. 27; substitution $\\mathrm{tpw}(G)\\le 10\\Delta(G)\\mathrm{tw}(G)$
  (Theorem 26) gives an explicit form of Thm. 19.
- `Toy test:` for grid $n\\times n$ we have $X=\\Delta\\,\\mathrm{tpw}=\\Theta(n)$.
  If you try to get the polynomial-size from the formula $2^{X^{4/d}}$, then it is natural to take $d\\asymp 4\\log_2 n/\\log_2\\log_2 n$ so that $X^{4/d}=\\Theta(\\log_2 n)$.
  But with such $d$ the condition of the lemma **is not satisfied**:
  $$X^{1/d}=2^{\\tfrac{\\log_2 X}{d}}=2^{\\tfrac14\\log_2\\log_2 n+o(1)}=(\\log_2 n)^{1/4+o(1)}\\ll 2d=\\Theta(\\tfrac{\\log_2 n}{\\log_2\\log_2 n}).$$
  Consequently, Section 16.119 fixes an explicit constant only in the $d$ "not too large" regime (when $X^{1/d}\\ge 2d$), but does not give a polynomialsize for $d=\\Theta(\\log_2 n/\\log_2\\log_2 n)$.
- `Status:` proven (conditional explicit constant; **not** closes Q39 without removing the condition).
- `Barrier check:` r--not applicable (upper bound in the restricted proof model), NP--not applicable, alg--not applicable.
- `Next step:` see Section 16.120: write down the unconditional upper from Claim 28 and estimate how much depth it actually requires for the polynomialsize.

### 16.120. Research step: GIRS'19 upper bound gives polynomial-size only at depth $\\Theta(\\log_2 n)$ (and at $\\Theta(\\log_2 n/\\log_2\\log_2 n)$ - only quasi-poly)

- `Lens:` Trade-off.
- `Statement:` Let $G$ be a connected graph, $T:=\\mathrm{Tseitin}(G,f)$ unsatisfiable, $d\\ge 1$ and $X:=\\Delta(G)\\,\\mathrm{tpw}(G)$.
  Then from the proof of GIRS'19 Thm. 27/Claim 28 follows upper
  $$\\mathrm{size}(T\\vdash\\bot)\\ \\le\\ \\mathrm{poly}(|T|)\\cdot 2^{\\,O\\bigl(d\\cdot X^{2/d}\\bigr)}.$$
  For grid $n\\times n$ (where $X=\\Theta(n)$ and number of variables $N=\\Theta(n^2)$) this means:
  1) at depth $d=\\Theta(\\log_2 n/\\log_2\\log_2 n)$ only $\\mathrm{size}=2^{(\\log_2 n)^{\\omega(1)}}$ (quasi-poly) is guaranteed, and
  2) in order to obtain the polynomialsize from this estimate, it is sufficient and essentially necessary to take $d=\\Theta(\\log_2 n)=\\Theta(\\log_2 N)$.
- `Proof:`
  1) The formula $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ is Section 16.115 (derived directly from Claim 28 and the choice $t_i=X^{2/d}$).
  2) Let $L:=\\ln X$ and set $f(d):=d\\cdot X^{2/d}=d\\,e^{2L/d}$.
     If $d=\\alpha\\,L/\\ln L$, then $X^{2/d}=e^{2L/d}=e^{2\\ln L/\\alpha}=L^{2/\\alpha}$ and therefore
     $$f(d)=\\Theta\\!\\left(\\frac{L}{\\ln L}\\cdot L^{2/\\alpha}\\right)=\\Theta\\!\\left(\\frac{L^{1+2/\\alpha}}{\\ln L}\\right)=\\omega(L).$$
     This means that the exponent in $2^{O(f(d))}$ is strictly greater than $\\Theta(\\ln X)$, and the polynomial-size is not guaranteed.
  3) If $d=\\Theta(L)$, then $X^{2/d}=e^{\\Theta(1)}=\\Theta(1)$ and therefore $f(d)=\\Theta(L)$; hence
     $2^{O(f(d))}=2^{\\Theta(\\ln X)}=\\mathrm{poly}(X)$.
     For grid $X=\\Theta(n)$ this gives a polynomialsize with $d=\\Theta(\\ln n)=\\Theta(\\ln N)$.
- `Toy test:` for $d=\\ln X$ we have $X^{2/d}=X^{2/\\ln X}=e^2$ and the exponent $\\asymp e^2\\ln X$; for $d=\\ln X/\\ln\\ln X$
  we have $X^{2/d}=(\\ln X)^2$ and the exponent $\\asymp (\\ln X)^3/\\ln\\ln X$.
- `Status:` proven (explains why "59 vs $c$" from Q39 does not close through the current GIRSupper).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` look for another upper-argument (not through "refinement-parity" in the style of Section 16.115), which gives a polynomial-size already at a depth of $O(\\log_2 n/\\log_2\\log_2 n)$, or an obvious barrier to such an improvement in Frege without XOR gates.

### 16.121. Research step: optimization $f(d)=d\\,X^{2/d}$ (within Claim 28)  polynomialsize certificate requires $d=\\Omega(\\ln X)$

- `Lens:` Trade-off.
- `Statement:` Let $X\\ge 2$ and $f(d):=d\\,X^{2/d}$ for $d>0$ (real).
  Then:
  1) (**Lower bound for a polynomialsize certificate.**) If $d=o(\\ln X)$, then $f(d)=\\omega(\\ln X)$, and therefore from the upper form
     $\\mathrm{poly}(|T|)\\cdot 2^{O(f(d))}$ cannot be printed polynomialsize.
  2) (**Optimal choice within this estimate.**) $f$ is minimal for $d=2\\ln X$, and $\\min f(d)=2e\\ln X=\\Theta(\\ln X)$.
     In particular, bound from Claim 28 does give a polynomialsize at depth $d=\\Theta(\\ln X)$ (but not at $o(\\ln X)$).
- `Proof:`
  We write $X^{2/d}=e^{2\\ln X/d}$ and set $t:=2\\ln X/d$ (so $d=2\\ln X/t$). Then
  $$\\frac{f(d)}{\\ln X}=\\frac{2e^{t}}{t}.$$
  1) If $d=o(\\ln X)$, then $t=2\\ln X/d\\to\\infty$, and therefore $e^{t}/t\\to\\infty$, that is, $f(d)/\\ln X\\to\\infty$ and $f(d)=\\omega(\\ln X)$.
  2) The derivative $f'(d)=e^{2\\ln X/d}\\cdot(1-2\\ln X/d)$, therefore the minimum is achieved at $d=2\\ln X$ and is equal to
     $f(2\\ln X)=2\\ln X\\cdot e=2e\\ln X$.
- `Toy test:` if $X=2^{64}$, then $\\ln X\\approx 44.36$ and the optimum is at $d\\approx 88.7$, where $f(d)\\approx 2e\\ln X\\approx 241$ (the exponent $2^{O(241)}$ is a polynomial in $X$).
- `Status:` proven (local "technique barrier": Claim28upper by itself does not give a polynomialsize for $d=o(\\ln X)$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` for Q39, look for an upper source/receiver, where the upper estimate is $2^{O(X^{c/d})}$ without the additional factor $d$ in the exponent (or explain why such a technique is not possible in Frege without XOR gates).


-/
