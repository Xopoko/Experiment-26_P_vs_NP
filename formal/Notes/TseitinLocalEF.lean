import Paperproof

/-!

# P vs NP - research steps 16.153-16.273 (flat localEF(s): Q41-Q43)

Main index: `P_vs_NP.md`.

### 16.153. Exploratory step: "circuit-lines" = extension variables  circuit-Frege p-simulated by EF (and vice versa), so saving representability via sharing actually puts the Q39 into EF mode

- `Lens:` Equivalence.
- `Statement:` Let $C$ be a De Morgan-**circuit** (DAG) of size $S$ and depth $d$ over inputs $x_1,\\dots,x_m$.
  Then there is an extension of variables $\\{p_g\\}_{g\\in\\mathrm{Gates}(C)}$ and a set of extension axioms (one per gate)
  $$p_g\\ \\leftrightarrow\\ \\mathrm{op}_g\\bigl(p_{g_1},\\dots,p_{g_k}\\bigr)$$
  such that in EF one can "represent" the value of the circuit by a formula of size $O(S)$ and depth $O(d)$: the output variable $p_{\\mathrm{out}}$ plays the role of the result $C(x)$.
  Therefore, any proof system in which lines are allowed as sharing is essentially the same (pequivalent) to EF: sharing  abbreviations via extension variables (see also Buss'97, Section 5.1 for motivation).
- `Proof:`
  1) (Encoding the circuit with extension variables.) For each input literal we set $p_{x_i}:=x_i$, $p_{\\neg x_i}:=\\neg x_i$.
     For each internal gate $g$ of the circuit with children $g_1,\\dots,g_k$, we introduce a fresh variable $p_g$ and add an extension formula
     $$p_g\\leftrightarrow (p_{g_1}\\vee\\cdots\\vee p_{g_k})\\quad\\text{or}\\quad p_g\\leftrightarrow (p_{g_1}\\wedge\\cdots\\wedge p_{g_k})$$
     (or $p_g\\leftrightarrow\\neg p_{g_1}$ if $g$ is a NOT gate). These formulas have size $O(k)$ and constant alternation depth.
  2) (Why is this a "representation".) After adding all the extension formulas, we get that each $p_g$ (under any assignment $x$) is equal to the value of the sub-circuit $C_g(x)$; in particular, $p_{\\mathrm{out}}$ evaluates $C(x)$.
     In terms of "representing parity" from HR Section 1.2, this means: if parity is calculated by a circuit of depth $d$ and size $M$, then it will automatically be represented by an EF line of size $O(M)$ and depth $O(d)$ (due to extension variables, i.e. DAG sharing).
  3) (Connection with circuitFrege.) "Fregelines as circuits" can be considered as Frege with DAGsharing allowed within the line; By replacing each common subnode of the circuit with an extension variable, we get EF mode with polynomial overhead in size.
     The reverse direction is trivial: the EF line is already a formula with extension variables, which means it calculates some DAG scheme (where extension variables play the role of nodes with fan-out $>1$).
- `Toy test:` the diagrams from Section 16.152 for $\\mathrm{PARITY}_{t^{d-1}}$ of depth $d$ and size $2^{O(t)}\\mathrm{poly}(t)$ turn into EF representations of the same size, i.e. with $t=\\Theta(\\log M)$ they give a "block" $(\\log M)^{d-1}$ without contradicting Rossman'16 (because Rossman is about **formulas** without sharing).
- `Status:` it has been proven: "fixing" representability by moving from formulas to diagrams means moving to EF/circuitFrege (abbreviations); So the next question is Q39 - are LB Hastad'20/HR'22 applicable to such an enhanced regime.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` in Hastad'20/HR'22, find the point where fan-out 1 (tree) is required in the switching/evaluation argument, and decide: (a) LB extends to the circuit-Frege/EF-variant, or (b) this is where the non-relativizing/non-natural step is needed.

### 16.154. Research step: EF gives a polynomialsize refutation Tseitin(Grid) already at $O(1)$depth (in terms of $\\vee/\\neg$), so LB Hastad'20 fundamentally does not extend to EF/circuitFrege

- `Lens:` Model stress test (what breaks when the model is strengthened).
- `Statement:` For any degree-bounded graph $G$ and charge $\\chi$ with $\\bigoplus_{v\\in V}\\chi(v)=1$ there is an EF-refutation
  $F:=\\mathrm{TseitinCNF}(G,\\chi)$ of polynomial size, in which **each row has a constant depth** in the sense of HR/Hastad (alternating $\\vee/\\neg$).
  In particular, for grid this gives polysize refutation with a depth of $O(1)$.
  Therefore, any attempt to extend the lower bound of Hastad'20 (Cor. 6.6) from boundeddepth Frege to "circuitFrege"/EF is impossible: EF already bypasses the $\\Omega(\\log N/\\log\\log N)$ threshold.
- `Proof:`
  1) (EF-framework.) See Section 16.88: introduce extension variables $p_v$ for XOR equations at vertices and variable $P:=\\bigoplus_v p_v$.
     From the equivalence of clauses  XOR equations we obtain $p_v\\leftrightarrow\\chi(v)$, whence $P\\leftrightarrow\\bigoplus_v\\chi(v)=1$ and, therefore, $P$.
     On the other hand, expanding the definitions of $p_v$ and rearranging XOR (association/commutativity + abbreviation $x\\oplus x\\leftrightarrow 0$), we get
     $$P\\leftrightarrow\\bigoplus_{v\\in V}\\ \\bigoplus_{e\\ni v} x_e\\leftrightarrow\\bigoplus_{e\\in E}(x_e\\oplus x_e)\\leftrightarrow 0,$$
     that is, $\\neg P$. Contradiction.
  2) (Why is the depth $O(1)$.) Each extension step is given by the constant depth formula:
     binary XOR $a\\oplus b$ is a constant formula in the basis $\\{\\vee,\\neg\\}$ (via $\\wedge:=\\neg(\\neg\\cdot\\vee\\neg\\cdot)$), and extension axioms have the form $p\\leftrightarrow\\varphi$ with $\\varphi$ of constant depth.
     Associativity/commutativity/XOR abbreviation in Section 16.88 are tautologies on a constant number of variables, which means they can be instantiated in EF without increasing the depth of lines (lines contain only variables $p_*$, $x_*$ and constants).
  3) (Connection with circuitFrege.) By Section 16.153, any "linecircuit/sharing" is pequivalent to EF via extension variables, so circuit mode does have the same effect: line depth can remain constant, hiding greater circuit depth in abbreviations.
- `Toy test:` for 3regular $G$, the formulas $p_v\\leftrightarrow(x_{e_1}\\oplus x_{e_2}\\oplus x_{e_3})$ and XOR rearrangement steps use only constant patterns (Section 16.88), and the number of extension variables introduced is $O(|V|+|E|)$.
- `Status:` proven (stress test shows: threshold LB Hastad'20 - essentially about **formulas** fan-out 1; in EF/circuit-Frege depth is not a limitation).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` in Hastad'20, explicitly indicate that the proof only works for Frege without extension variables, and localize in the switching/evaluation argument the place where the attempt to include extension variables fails (you need to "consistently" restrict new variables, i.e. calculate the hidden scheme).

### 16.155. Research step: the point where Hastad'20 strictly uses "variables = edges" (fanout 1 essentially) - locality via $\\mathrm{supp}(\\alpha)\\subseteq V$; extension variables break this locality and therefore are not included in the switching/evaluationframework

- `Lens:` Model stress test (localize dependence on the model).
- `Statement:` In Hastad'20, the local technique (restrictions + evaluations) relies on the fact that **each variable corresponds to an edge** and therefore "affects" only the two ends of the edge: for partial assignment $\\alpha$ is defined
  $$\\mathrm{supp}(\\alpha)\\subseteq V\\quad\\text{as the set of vertices adjacent to the assigned variables}$$
  (Hastad'20, Section 3: definitions of "complete assignment", "support", "locally consistent", see `../../resources/downloads/hastad_2020_small_depth_frege_tseitin_grids.pdf`, paragraph starting with "On a set $X$ of nodes ..." and Definition 3.1).
  This implies a key invariant: a decision-tree path of depth $t$, reading only edge variables, specifies an assignment with
  $$|\\mathrm{supp}(\\alpha)|\\le 2t.$$
  Therefore, "small depth" automatically means "small geometric support" on the grid, and we can talk about the giant component and the closure $\\mathrm{cl}(X)$.
  For EF/circuit-Frege, extension variables $p$ are not edge variables: if you treat $p$ as a reduction of a global function of many edges (for example, PARITY of a large block), then it has little support, and the invariant $|\\mathrm{supp}(\\alpha)|\\le O(t)$ for depth $t$ breaks down with just one query of $p$.
  Therefore, the Hastad technique (in its current form) is **not intended** for EF/circuit-Frege: either $p$ is considered a "free" variable without support (then the meaning of extension axioms is lost), or $\\mathrm{supp}(p)$ becomes large and breaks local lemmas.
- `Proof:`
  1) (Locality of edge variables.) In Tseitin(G) each variable $x_e$ corresponds to an edge $e=\\{u,v\\}$, which means that when assigning $x_e:=b$ only $u,v$ are added to the support.
     Therefore, if a decision tree asks $t$ different $x_e$, then the set of affected vertices has size $\\le 2t$.
  2) (Where this is used.) In Section 3, Hastad'20 considers partial assignments with $|X|\\le 2n/3$ (where $X=\\mathrm{supp}(\\alpha)$) and deduces the existence of a "giant component" in the complement of $X^c$ and the correctness of the concept $\\mathrm{cl}(X)$; this is fundamental for "locally consistent" and for evaluations to work with shallow trees.
  3) (Counter-example with an extension variable.) Let an extension variable $p\\leftrightarrow\\bigoplus_{e\\in E'} x_e$ be introduced into EF for a set of edges $E'$ of size $\\Theta(n)$ (for example, the boundary of a large rectangle).
     If we try to include $p$ in the same geometry, it is natural to put $\\mathrm{supp}(p):=\\bigcup_{e\\in E'}\\mathrm{supp}(x_e)$, which has size $\\Theta(n)$.
     Then one request $p$ (depth 1) already generates $|\\mathrm{supp}(\\alpha)|=\\Theta(n)$, and the connection "depth  small support" disappears.
     If we declare $\\mathrm{supp}(p)=\\varnothing$ (to preserve $|\\mathrm{supp}(\\alpha)|\\le 2t$), then "locally consistent" ceases to control the consistency of $p$ with edges and extension axioms: the value of $p$ can be chosen independently of $x$ without increasing the support, which is exactly what the EF bypass gives (Section 16.154).
- `Toy test:` the global variable $P$ from Section 16.88 (XOR of all vertex $p_v$) in "support-by-sense" affects the entire mesh, but as an atomic variable has depth 1; this is incompatible with the invariant $|\\mathrm{supp}(\\alpha)|\\le 2t$.
- `Status:` proven as localization: the "fanout 1 / variables=edges" point is built into the support/closure geometry itself; therefore HastadLB is not transferred to EF/circuitFrege without new technology.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to formulate an intermediate "local-EF" model: allow extension variables only with $|\\mathrm{supp}(p)|\\le \\mathrm{polylog}(n)$, and check whether the EF-proof of depth $o(\\log n/\\log\\log n)$ remains possible or whether the Hastad'20 technique starts to work.

### 16.156. Exploratory step: "localEF(s)" (extension variables with limited geometric support) and fact: Tseitin's EF refutation via global XOR inevitably introduces a variable with $\\Omega(|V|)$ support

- `Lens:` Invariant (geometric support).
- `Definition (formula support):` For Tseitin on the graph $G=(V,E)$ and the formula $\\varphi$ over edge variables $\\{x_e\\}_{e\\in E}$ we set
  $$\\mathrm{supp}(\\varphi):=\\bigcup\\{\\{u,v\\}: e=\\{u,v\\}\\in E\\text{ and }x_e\\text{ occurs in }\\varphi\\}\\ \\subseteq V.$$
- `Definition (localEF(s)):` Let us call an EF proof $s$-local if for each extension step $p\\leftrightarrow\\varphi$ holds
  $$|\\mathrm{supp}(\\varphi)|\\le s.$$
  (That is, only "local" subformulas along the vertices of the graph are allowed to reduce.)
- `Statement:` The EF-refutation of Tseitin(Grid) from Section 16.88/Section 16.154 is **not** $s$-local for any $s=o(|V|)$:
  it inevitably contains an extension variable $P$ with $|\\mathrm{supp}(P)|=\\Omega(|V|)$.
- `Proof:`
  1) In Section 16.88, the variable $P\\leftrightarrow\\bigoplus_{v\\in V} p_v$ is introduced, where each $p_v$ encodes the local parity of incident edges of vertex $v$.
  2) For grid, each vertex has a constant degree, which means $|\\mathrm{supp}(p_v)|=O(1)$, but
     $$\\mathrm{supp}(P)=\\bigcup_{v\\in V}\\mathrm{supp}(p_v)=V,$$
     since each $p_v$ depends on the edges incident to $v$.
     Therefore, $|\\mathrm{supp}(P)|=|V|=\\Theta(n^2)$.
  3) So this EF proof requires $s\\ge |V|$; with $s=\\mathrm{polylog}(n)$ it does not fall into localEF(s).
- `Toy test:` for torus-grid $|V|=n^2$: even if all local $p_v$ have support $\\le 5$, variable $P$ has support $n^2$.
- `Status:` proven (the local version of EF excludes the "global XOR" bypass).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` understand whether it is possible to do without a global variable of type $P$ in localEF($\\mathrm{polylog}(n)$), or whether any polysize refutation should "inflate" support somewhere; try to adapt the support-oriented version of the Hastad'20 evaluation method to local-EF(s).

### 16.157. Exploratory step: in localEF(s) locality is restored with the loss of $\\times s$: decision tree of depth $t$ gives assignment with $|\\mathrm{supp}|\\le O(s\\,t)$ (if support for extension variables is defined through their formulas)

- `Lens:` Invariant.
- `Statement:` Consider a proof line/formula over edge variables $\\{x_e\\}$ and extension variables $\\{p_i\\}$, where each $p_i$ is introduced by the rule extension $p_i\\leftrightarrow\\varphi_i(x)$ and $|\\mathrm{supp}(\\varphi_i)|\\le s$ (that is, we are in localEF(s) under Section 16.156).
  Let's define variable support as
  $$\\mathrm{supp}(x_{\\{u,v\\}}):=\\{u,v\\},\\qquad \\mathrm{supp}(p_i):=\\mathrm{supp}(\\varphi_i).$$
  Then any decision tree $T$ of depth $t$, which asks only for variables from $\\{x_e\\}\\cup\\{p_i\\}$, generates along any path a partial assignment $\\alpha$ with
  $$|\\mathrm{supp}(\\alpha)|\\le (2+s)\\,t.$$
  Therefore, for $s=\\mathrm{polylog}(n)$ the invariant "small depth $\\Rightarrow$ small geometric support" (from Hastad'20/HR'22, Section 3) is carried over to localEF(s) with the loss of the factor $s$.
- `Proof:` Let a path in $T$ contain $t$ queries.
  Each request for the edge variable $x_e$ adds no more than 2 vertices to support.
  Each request for the extension variable $p_i$ by definition adds at most $|\\mathrm{supp}(\\varphi_i)|\\le s$ vertices.
  Therefore, in total by subditivity
  $$|\\mathrm{supp}(\\alpha)|\\le 2\\cdot(\\#\\text{edge-queries})+s\\cdot(\\#\\text{ext-queries})\\le (2+s)t.$$
- `Toy test:` if $s=5$ and $t=100$, then $|\\mathrm{supp}(\\alpha)|\\le 700$, i.e. such a branch "sees" only a local fragment of the grid and remains in giant component/closure mode for large $n$.
- `Status:` proven (this is the first formal bridge "evaluation method + local extension variables": locality does not disappear, but degrades by a factor of $s$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to rewrite Definition 2.11 (tevaluation) HR'22 with support that takes into account extension variables, and check whether the key lemmas are "locally consistent" under the condition $|\\mathrm{supp}(\\varphi_i)|\\le s$ (parameters should change as $t\\mapsto t\\cdot s$).

### 16.158. Exploratory step: eliminating queries for extension variables in the decision tree (local-EF(s)  edge-only DT with depth $O(s\\,t)$)

- `Lens:` Equivalence (query model: $x$ vs $(x,p)$).
- `Statement:` Let $G=(V,E)$ be a graph of maximum degree $\\Delta$ (for grid: $\\Delta\\le 4$).
  Consider edge variables $\\{x_e\\}_{e\\in E}$ and extension variables $\\{p_i\\}$, where for each $i$ an extension step is specified
  $$p_i\\leftrightarrow\\varphi_i(x)\\qquad\\text{i}\\qquad |\\mathrm{supp}(\\varphi_i)|\\le s.$$
  Let $\\mathrm{vars}(\\varphi_i)$ denote the set of **different** edge-variables occurring in $\\varphi_i$ and set
  $$m:=\\max_i |\\mathrm{vars}(\\varphi_i)|\\le \\Delta s/2.$$
  Then for any decision tree $T$ of depth $t$ that can ask for variables from $\\{x_e\\}\\cup\\{p_i\\}$, there is a decision tree $T_x$ over some edge variables $\\{x_e\\}$ of depth $\\le (1+m)\\,t$ such that for any complete assignment $a\\in\\{0,1\\}^E$
  $$T_x(a)\\ =\\ T\\bigl(a,\\ (\\varphi_i(a))_i\\bigr),$$
  those. $T_x$ simulates $T$ on **consistent** assignments, where $p_i=\\varphi_i(x)$.
  In particular, on grid the depth increases to no more than $(1+2s)\\,t=O(s\\,t)$.
- `Proof:`
  1) (Evaluate $m$.) Each variable $x_{\\{u,v\\}}$ adds vertices $u,v$ to $\\mathrm{supp}(\\varphi_i)$, so all edges from $\\mathrm{vars}(\\varphi_i)$ lie inside the induced subgraph on $\\mathrm{supp}(\\varphi_i)$.
     For degree $\\le\\Delta$, the number of edges in such a subgraph does not exceed $\\Delta|\\mathrm{supp}(\\varphi_i)|/2\\le \\Delta s/2$, whence $|\\mathrm{vars}(\\varphi_i)|\\le \\Delta s/2$.
  2) (Local replacement of query $p_i$.) Let us fix the order of variables from $\\mathrm{vars}(\\varphi_i)$.
     Let's build a decision tree $D_i$ of depth $|\\mathrm{vars}(\\varphi_i)|$, which sequentially queries these edge variables and in the sheet calculates the value of the Boolean formula $\\varphi_i$ on the collected values.
     Then querying $p_i$ into $T$ (on consistent assignments) is equivalent to traversing $D_i$ and then going to the corresponding child ("$p_i=0$" or "$p_i=1$").
  3) (Global simulation.) Let us replace in $T$ each internal node asking $p_i$ with a copy of $D_i$ with the leaves glued together according to the previous point.
     We get a tree $T_x$ asking only edge variables. By depth: each initial request for an edge variable gives +1, each request $p_i$ gives +$|\\mathrm{vars}(\\varphi_i)|\\le m$, which means for any path
     $$\\mathrm{depth}_{T_x}\\le (\\#\\text{edge queries})+m\\cdot(\\#\\text{ext queries})\\le (1+m)\\,t.$$
     Correctness on $a$ follows from induction on the structure of the tree: at node $p_i$ a new fork selects a branch exactly along $\\varphi_i(a)$.
- `Toy test:` if $p\\leftrightarrow(x_{e_1}\\oplus x_{e_2}\\oplus x_{e_3})$ (local XOR on 3 edges), then the query $p$ is replaced by three queries $x_{e_1},x_{e_2},x_{e_3}$ and a parity calculation in the leaf; this is $D_i$ for $|\\mathrm{vars}(\\varphi)|=3$.
- `Status:` proven (the query model for $p$ "collapses" into a query model for $x$ with a multiplicative loss of $O(s)$ on boundeddegree graphs).
- `Barrier check:` r - applicable (purely syntactic simulation, relativized), NP - not applicable (not a "natural property"), alg - not applicable (no arithmetization).
- `Next step:` apply this as a technical lemmatizer when trying to migrate HR'22: allow $p_i$ queries (for local-EF(s)) in the definition of $t$-evaluation, then replace them with edge-queries and ensure that all thresholds in the "locally consistent/closure" lemmas are preserved for $t\\mapsto O(s\\,t)$.

### 16.159. Research step: draft "HRevaluation for localEF(s)" through extended support and $s$cost of requests

- `Lens:` Invariant (geometric support = "visible area").
- `Statement (draft patch to HR'22, Section 2.4-2.7):` Let $X=\\{x_e\\}$ be edge variables $\\mathrm{Tseitin}(G_n)$ on the grid, and extension variables $P=\\{p_i\\}$ with axioms are allowed in the proof
  $$p_i\\leftrightarrow\\varphi_i(X),\\qquad |\\mathrm{supp}(\\varphi_i)|\\le s,$$
  where $\\mathrm{supp}(\\varphi)$ is the set of vertices incident to edges whose variables occur in $\\varphi$ (as in HR'22: $\\mathrm{supp}(x_{\\{u,v\\}})=\\{u,v\\}$).
  Then a natural generalization of HR'22 Definition 2.2 / Cor. 2.7 is like this:

  1) (**Extended assignment support.**) For partial assignment $\\alpha$ to $X\\cup P$ set
     $$\\mathrm{supp}_s(\\alpha):=\\mathrm{supp}(\\alpha\\!\upharpoonright_X)\\ \\cup\\ \\bigcup_{p_i\\in\\mathrm{dom}(\\alpha)}\\mathrm{supp}(\\varphi_i).$$

  2) (**$s$-local consistency.**) $\\alpha$ is called $s$-locally consistent if for $U=\\mathrm{supp}_s(\\alpha)$ there is $\\beta$ on $X$, *complete on* $\\mathrm{closure}(U)$ (in the sense of HR: assigns all edge-variables incident $\\mathrm{closure}(U)$), such that:
     (i) $\\beta$ extends $\\alpha\\!\upharpoonright_X$; (ii) satisfies all parity-constraints on $\\mathrm{closure}(U)$; (iii) for all assigned $p_i$, $\\alpha(p_i)=\\varphi_i(\\beta)$ holds.

  3) (**Cost of the branch/tree.**) For the branch $\\tau$ decision tree (on variables $X\\cup P$) we set
     $$\\mathrm{cost}_s(\\tau):=2\\cdot\\#(x\\text{-queries in }\\tau)+\\sum_{p_i\\in\\mathrm{dom}(\\tau)}|\\mathrm{supp}(\\varphi_i)|,$$
     and $\\mathrm{cost}_s(T):=\\max_{\\tau\\in T}\\mathrm{cost}_s(\\tau)$, so roughly $\\mathrm{cost}_s(T)\\le (s+2)\\,\\mathrm{depth}(T)$.

  4) (**Expected analogue of HR Cor. 2.7.**) If $\\alpha$ $s$locally consistent and
     $$|\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(T)\\le n/2,$$
     then "trimmed restriction" $T\\lceil\\alpha$ (like HR, but with pairwise $s$local consistency) is correct and again $s$locally consistent.

  In this form, you can try to transfer HR'22 Definition 2.11 (tevaluation) to localEF(s), replacing all thresholds of the form
  $|\\mathrm{supp}(\\alpha)|+2\\,\\mathrm{depth}(T)\\le n/2$ by $|\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(T)\\le n/2$ (or more roughly $t\\mapsto O(s\\,t)$).
- `Toy test:` if $p\\leftrightarrow(x_{e_1}\\oplus x_{e_2}\\oplus x_{e_3})$, then the request $p$ "costs" 3 edges/6 ends; this is consistent with Section 16.158 (query $p$ is expanded into 3 edge queries).
- `Status:` draft (a careful check is needed: where exactly in the HR'22 proofs is it used that the variables are *exactly edges*, and that adding a query $p_i$ is correctly "paid" by the local witness on $\\mathrm{closure}(\\mathrm{supp}_s)$).
- `Barrier check:` r - applicable (the entire support/closure/DT scheme is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q41: (a) choose the exact model localEF(s) (we prohibit $\\varphi_i(P)$ or consider $\\mathrm{supp}(p_i)$ as support for the fully expanded formula), (b) formally prove (or find a counterexample) item (4) as an analogue of Cor. 2.7, and only after that try to transfer Lemma 2.13 (the threshold $t\\le n/16$ becomes $t\\le \\Theta(n/s)$).

### 16.160. Exploratory step: counterexample - "nested extension" without fully deploying support makes localEF(s) meaningless

- `Lens:` Model stress test.
- `Statement (counterexample to "naive nestedlocality"):`
  Let extension axioms of the form $p\\leftrightarrow\\varphi(X,P_{<p})$ be allowed, and the "naive support" of a step is measured only by *syntactically occurring edge variables* in $\\varphi$ (extension variables are considered atoms and are not expanded in $X$).
  Then there is a chain of extension steps, where **each** step has support $\\le 2$ (one edge variable), but the resulting variable calculates the XOR of $m$ edge variables and therefore has "true" support $\\Theta(m)$.
  Therefore, without disabling nesting or without deploying support, the definition of localEF(s) ceases to control the geometry (and cannot serve as the basis for $\\mathrm{supp}_s/\\mathrm{cost}_s$version of Cor. 2.7).
- `Proof (explicit construction):`
  Let's take pairwise different edge variables $x_{e_1},\\dots,x_{e_m}$ and introduce extension variables $p_1,\\dots,p_m$:
  $$p_1\\leftrightarrow x_{e_1},\\qquad p_i\\leftrightarrow (p_{i-1}\\oplus x_{e_i})\\ \\ (2\\le i\\le m).$$
  (The operation $\\oplus$ is expressed by a constant size formula in the basis $\\vee,\\wedge,\\neg$.)
  Then by induction $p_i\\equiv\\bigoplus_{j\\le i}x_{e_j}$.
  With naive support calculation, each $\\varphi_i$ contains **exactly one** edge variable $x_{e_i}$, so $|\\mathrm{supp}(\\varphi_i)|=2$ for all $i$.
  But the "expanded" formula for $p_m$ contains all $x_{e_1},\\dots,x_{e_m}$, so
  $$\\mathrm{supp}(p_m)=\\bigcup_{j\\le m}\\mathrm{supp}(x_{e_j}).$$
  In particular, if we choose edges $e_j$ in pairs without common ends, then $|\\mathrm{supp}(p_m)|=2m$.
- `Toy test:` on $n\\times n$ grid we can take $m=\\lfloor n^2/2\\rfloor$ pairs of disjoint edges (matching); then "naive" $s=2$, but $|\\mathrm{supp}(p_m)|=\\Theta(n^2)$.
- `Status:` counterexample (fixes the choice of model: either flat $\\varphi_i(X)$ or $\\mathrm{supp}(p_i)$ is calculated using a fully expanded formula in $X$).
- `Barrier check:` r - applicable (purely a syntactic trick), NP - not applicable, alg - not applicable.
- `Next step:` for Q41, accept the "flat" (prohibition $\\varphi_i(P)$) or "unfoldedsupport" model and prove/refute the analogue of HR Cor in it. 2.7 for $\\mathrm{supp}_s/\\mathrm{cost}_s$.

### 16.161. Exploratory step: evidence of an analogue of HR Cor. 2.7 for **flat** localEF(s) via $\\mathrm{supp}_s/\\mathrm{cost}_s$

- `Lens:` Invariant.
- `Statement (Q41.S3-proof-cor27-analogue-flat):`
  We work in the **flat** model: extension axioms have the form
  $$p_i\\leftrightarrow\\varphi_i(X),\\qquad |\\mathrm{supp}(\\varphi_i)|\\le s,$$
  where $X$ are edge variables of Tseitin($G_n$), and $\\varphi_i$ does not contain extension variables.
  We use the definitions of $\\mathrm{supp}_s(\\alpha)$, $s$local consistency, and $\\mathrm{cost}_s(T)$ from Section 16.159.
  Then a direct analogue of HR'22 Cor is performed. 2.7 (p. 8; PDF p. 10) with $|\\mathrm{supp}(\\alpha)|+2\\,\\mathrm{depth}(T)$ replaced by
  $|\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(T)$:
  if $T$ is a (usual) decision tree over the variables $X\\cup P$ and $\\alpha$ $s$locally consistent, and
  $$|\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(T)\\le n/2,$$
  then "trimmed restriction" $T\\lceil\\alpha$ (like HR, but pairwise $s$local consistency) is correct and is $s$locally consistent decision tree
  (specifically $T\\lceil\\alpha\\ne\\varnothing$).
- `Proof:`
  It is enough to show that there is at least one branch $\\tau$ of the tree $T$ such that $\\alpha\\cup\\tau$ $s$locally consistent.
  Let's build it greedily, going down from the root to the leaf.
  At the step we have a partial assignment
  $$\\gamma:=\\alpha\\cup\\tau_{\\le k}$$
  (branch prefix), which is $s$locally consistent, and set $U:=\\mathrm{supp}_s(\\gamma)$.
  For any vertex of the tree $T$, any branch prefix has $\\mathrm{cost}_s(\\tau_{\\le k})\\le \\mathrm{cost}_s(T)$, so by condition
  $$|U|\\le |\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(\\tau_{\\le k})\\le |\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(T)\\le n/2.$$
  Consider the next query variable in $T$ (at the current node) and choose a value that preserves $s$-local consistency.
  1) **Edge-query $x_e$.**
     From $s$local consistency for $\\gamma$ there is a witness $\\beta$ on $X$, complete on $\\mathrm{closure}(U)$, satisfying parityconstraints on $\\mathrm{closure}(U)$ and consistent with all assigned $p_j$.
     Let $E_P$ denote the set of edge variables occurring in $\\varphi_j$ for all $p_j\\in\\mathrm{dom}(\\gamma)$.
     Let's extend $\\gamma\\!\upharpoonright_X$ to a partial assignment of $\\delta$ on $X$, assigning all variables from $E_P$ as in $\\beta$.
     Then $\\mathrm{supp}(\\delta)\\subseteq U$, and $\\delta$ is locally consistent in the sense of HR Definition 2.2 (witness is the same $\\beta$).
     By HR Lemma 2.3 (p. 6; PDF p. 8) there is a locally consistent $\\delta'\\supseteq\\delta$ with $x_e$ in the domain.
     Let $b:=\\delta'(x_e)$. Then $\\gamma':=\\gamma\\cup\\{x_e\\mapsto b\\}$ $s$locally consistent:
     all previously assigned $p_j$ remain compatible, because their formulas $\\varphi_j$ use only variables from $E_P$ that are already fixed in $\\delta$ and therefore unchanged in $\\delta'$.
  2) **Extension request $p_i$.**
     Let $E_i:=\\mathrm{vars}(\\varphi_i)$ be the set of edge variables in $\\varphi_i$.
     Let's start with the same $\\delta$ (fixes $E_P$ by witness $\\beta$) and sequentially apply HR Lemma 2.3, adding variables from $E_i$ to the $\\delta$ domain.
     By construction, at each step the support remains in $U\\cup\\mathrm{supp}(\\varphi_i)$, and
     $$|U\\cup\\mathrm{supp}(\\varphi_i)|\\le |\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(\\tau_{\\le k})+|\\mathrm{supp}(\\varphi_i)|\\le |\\mathrm{supp}_s(\\alpha)|+\\mathrm{cost}_s(\\tau_{\\le k+1})\\le n/2,$$
     so the lemma applies.
     We obtain a locally consistent $\\delta'$ on $X$, which assigns all variables from $E_P\\cup E_i$.
     Let us put $b:=\\varphi_i(\\delta')$ and $\\gamma':=\\gamma\\cup\\{p_i\\mapsto b\\}$.
     Then $\\gamma'$ $s$locally consistent: witness is given by completion $\\delta'$ on $\\mathrm{closure}(U\\cup\\mathrm{supp}(\\varphi_i))$,
     and the equality $p_i=\\varphi_i(X)$ is satisfied by the definition of $b$.
  In both cases, we found the value for the next query, preserving $s$local consistency and the invariant $|\\mathrm{supp}_s(\\gamma')|\\le n/2$.
  Continuing to the leaf, we obtain a branch $\\tau$ with $\\alpha\\cup\\tau$ $s$locally consistent.
  This means that the set of branches pairwise $s$locally consistent with $\\alpha$ is non-empty, and the "trimmed restriction" $T\\lceil\\alpha$ is defined and $s$locally consistent (by definition).
- `Toy test:` if $p\\leftrightarrow x_e$ (support 2), then the "extension query" case literally reduces to HR Lemma 2.3 for $x_e$.
- `Status:` proven (in the flat model; removes the main risk in Section 16.159: the constraint "the branch is small  closure-witness exists" is transferred to local-EF(s) when $2\\,\\mathrm{depth}$ is replaced by $\\mathrm{cost}_s$).
- `Barrier check:` r - applicable (the argument is entirely about support/closure/decision trees and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` using this analog Cor. 2.7, rewrite HR Definition 2.11 (tevaluation) for flat localEF(s) and check where in Lemma 2.13 the threshold needs to be controlled more precisely (expectedly $t\\le\\Theta(n/s)$).

### 16.162. Research step: flat localEF(s) - "tevaluation" and transfer of HR Lemma 2.13 with threshold $t\\le\\Theta(n/s)$

- `Lens:` Equivalence.
- `Definition (costt evaluation, flat localEF(s)):` Let us fix $n\\times n$ grid $G_n$, edge variables $X$ and extension variables $P$ with axioms
  $$p_i\\leftrightarrow\\varphi_i(X),\\qquad |\\mathrm{supp}(\\varphi_i)|\\le s,$$
  where $\\varphi_i$ does not contain variables from $P$ (flat).
  We say that the set of formulas $\\Gamma$ has **cost$t$evaluation** $\\phi$ if $\\phi$ maps each formula $F\\in\\Gamma$ to $s$locally consistent decision tree $\\phi(F)$ with
  $$\\mathrm{cost}_s(\\phi(F))\\le t,$$
  and executes Properties 1-4 from HR'22 Definition 2.11 (PDF p. 11), but with "locally consistent" replaced by "$s$locally consistent".
- `Statement (analogous to HR Lemma 2.13):`
  Let $t\\le n/16$ and there exist a Frege-derivation of the formula $A$ from Tseitin($G_n$) (and, optionally, flat extension-axioms) such that **each** line has a cost-$t$-evaluation, and all these evaluations are pairwise functionally equivalent (as in HR'22 Definition 2.12).
  Then each line of output is displayed in a 1tree; in particular, $\\bot$ cannot be inferred.
- `Proof (reduced to HR):`
  Proof of HR'22 Lemma 2.13 (Appendix A.1, paper p. 47-48; PDF p. 50-51) is translated verbatim because it only uses:
  (i) Properties 1–4 evaluation,
  (ii) functional equivalence of evaluations,
  (iii) the fact that all constraints of the form $T\\lceil\\alpha$ and $T\\lceil(\\alpha\\cup\\tau)$ are correctly defined and give (s)locally consistent trees.

  In HR, clause (iii) is provided by Cor. 2.7 at $t\\le n/16$; in flat localEF(s) it is provided by Section 16.161, since for any branch $\\tau$ of tree $T$ we have
  $$|\\mathrm{supp}_s(\\tau)|\\le \\mathrm{cost}_s(\\tau)\\le \\mathrm{cost}_s(T)\\le t,$$
  and therefore for any other tree $T'$ with $\\mathrm{cost}_s(T')\\le t$:
  $$|\\mathrm{supp}_s(\\tau)|+\\mathrm{cost}_s(T')\\le 2t\\le n/2.$$
  Similarly, if in the Cut case it is necessary to limit by $\\tau\\cup\\tau'$, then
  $|\\mathrm{supp}_s(\\tau\\cup\\tau')|\\le |\\mathrm{supp}_s(\\tau)|+|\\mathrm{supp}_s(\\tau')|\\le 2t$ and
  $|\\mathrm{supp}_s(\\tau\\cup\\tau')|+\\mathrm{cost}_s(T'')\\le 3t\\le 3n/16<n/2$,
  so Section 16.161 applies.
  This means that all restricted trees used in HR induction are correct, and the conclusion "you cannot get a 0branch on a new line" is preserved.
- `Corollary (threshold $t\\le\\Theta(n/s)$ in terms of depth):`
  In the flat model, any decision tree of depth $d$ satisfies $\\mathrm{cost}_s(T)\\le (s+2)\\,d$ (see Section 16.159),
  so "depth$d$ evaluation" implies cost$t$ evaluation with $t:=(s+2)d$.
  In particular, the condition $t\\le n/16$ is equivalent to $d\\le n/(16(s+2))=\\Theta(n/s)$.
- `Toy test:` for $s=0$ (no extension variables) we have $\\mathrm{cost}_0=2\\,\\mathrm{depth}$, so the condition $t\\le n/16$ corresponds to $\\mathrm{depth}\\le n/32$ (the constants were not optimized; the scale $\\Theta(n)$ is important).
- `Status:` proven (flat model; gives an explicit "gatekeeper": the entire evaluation framework is transferred with the replacement $t\\mapsto (s+2)t$).
- `Barrier check:` r - applicable (the entire support/closure/DT construction is relativized), NP - not applicable, alg - not applicable.
- `Next step:` if you try to use this for lower bounds, you need to show: (a) why poly-size flat local-EF(s) output *induces* depth-$d$ evaluations with $d=\\mathrm{polylog}(n)$, or (b) where exactly multi-switching/representation breaks down in the presence of extension variables even in flat mode.

### 16.163. Research step: exact quote - where HR'22 builds tevaluation by induction on depth (Proof of Thm. 4.1)

- `Lens:` Invariant.
- `Statement:` In HR'22, an *inductive definition* of tevaluation is explicitly written for all subformulas of the "short and small" Fregeproof (after applying the full restrictions sequence); the only non-trivial domain extension occurs in the case of disjunction and is done through the switching lemma.
- `Proof/link:` Håstad–Risse, `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`:
  1) (paper p. 15; PDF p. 17) “For the total size lower bound we in fact do not create distinct t-evaluations per line but rather a single one, used on each line.”
  2) (paper p. 16; PDF p. 18) in the proof of Theorem 4.1 after formula (4) the definition of $\\phi_{i+1}$ is given for cases (quote):
     > “Consider any such formula $F\\in\\Gamma$. We define $\\phi_{i+1}$ as follows.
     > 1. If $F$ is of depth at most $\\mathrm{depth}(F)\\le i$, then we let $\\phi_{i+1}(F\\!\upharpoonright\\!\\sigma_i^*)=\\phi_i(F\\!\upharpoonright\\!\\sigma_i^{*\\! -1})\\!\upharpoonright\\!\\sigma_i$. By Lemma 3.4 the restricted $t_i$-evaluation $\\phi_i\\!\upharpoonright\\!\\sigma_i$ is defined on such formulas.
     > 2. If $F=\\neg F'$ is of depth $i+1$, then $\\phi_{i+1}(F\\!\upharpoonright\\!\\sigma_i^*)$ is defined in terms of $\\phi_{i+1}(F'\\!\\upharpoonright\\!\\sigma_i^*)$ by negating all the leaf labels.
     > 3. If $F=\\bigvee_j F_j$ is of depth $i+1$ and each $F_j$ is of depth at most $\\mathrm{depth}(F_j)\\le i$, then we appeal to Lemma 4.2 to obtain a decision tree $T$ … representing $\\bigvee_j T_j$ for $T_j=\\phi_i(F_j\\!\\upharpoonright\\!\\sigma_i^{*\\! -1})$.”
- `Toy test:` text extraction `pdftotext -f 18 -l 18` shows points 1-3 above verbatim (checking "where exactly evaluation is built").
- `Status:` known fact (exact reference to the evaluations construct).
- `Barrier check:` r - not applicable (at this step only quote localization), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, localize a similar "line-by-line" construction (functionally equivalent $t(\\eta)$evaluations) in the proof of Theorem 4.3/Lemma 4.5 and note where in this place the appearance of extension variables can break switching/representation.

### 16.164. Research step: exact quote - line-by-line construction of functionally equivalent $t(\\eta)$evaluations (Theorem 4.3 / Lemma 4.5)

- `Lens:` Equivalence.
- `Statement:` The proof of HR'22 Theorem 4.3 explicitly supports (i) for each line $\\nu$ of the proof - its own $t(\\eta)$evaluation $\\phi^\\eta_\\nu$ on the set of subformulas $\\Gamma^\\eta_\\nu$, (ii) for each line - a "general" partial decision tree $T_\\eta(\\nu)$, used to extend evaluations to next level of depth. The inductive step is fixed as Lemma 4.5 and uses the multiswitching lemma (Lemma 4.4) on $\\phi^{\\eta-1}_\\nu(F)\\!\upharpoonright\\!\\tau$ trees.
- `Proof/link:` Håstad–Risse, `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`:
  1) (Theorem 4.3, PDF p. 19) “The main difference is that instead of creating a single t-evaluation for the entire proof we in fact independently create t-evaluations for each line. These t-evaluations turn out to be functionally equivalent…”.
  2) (after (6), PDF p. 19) for each $\\eta$ we introduce
     $$\\Gamma^\\eta_\\nu:=\\{F\\!\upharpoonright\\!\\sigma^*_\\eta\\mid F\\in\\Gamma_\\nu\\ \\wedge\\ \\mathrm{depth}(F)\\le \\eta\\},\\tag{6}$$
     and functional equivalence of all $\\phi^\\eta_\\nu$ is required.
  3) (Lemma 4.5, PDF p. 20) inductive step (quote from statement):
     > “Suppose that for every line $\\nu\\in[N]$ we have functionally equivalent $t(\\eta-1)$-evaluations $\\phi^{\\eta-1}_\\nu$ … Suppose that $t(\\eta)\\le n_\\eta/16$. For $\\sigma_\\eta\\sim D_k\\Sigma(n_{\\eta-1},n_\\eta)$ with probability $1-N^{-1}$, for every line $\\nu$ … there are functionally equivalent $t(\\eta)$-evaluations $\\phi^\\eta_\\nu$ … and a $t$-common partial decision tree $T_\\eta(\\nu)$ …”.
- `Toy test:` `pdftotext -f 20 -l 20` shows Lemma 4.5 and within the proof an explicit definition of $\\phi^\\eta_\\nu$ by cases (depth< /  / ) using the constructed $T_\\eta(\\nu)$.
- `Status:` known fact (exact reference to "linewise evaluations" HR'22 framework).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` for Q43, highlight the place in the proof of Lemma 4.5 where it is used that $\\phi^{\\eta-1}_\\nu(F)$ trees query *only edge variables* and that full restrictions/local consistency are closed with respect to these queries; then check whether this step remains the same when adding flat extension variables (or fix the breaking point).

### 16.165. Research step: flat extensions - how to remove $P$ queries from decision trees (unfolding) at the cost of the $O(s)$ factor in depth

- `Lens:` Compression/canonization.
- `Statement (Q43.S3-check-lemma45-flat-ext-break):`
  Let us work on a $n\\times n$ grid and let **flat** extension variables $P$ with axioms be allowed
  $$p_i\\leftrightarrow\\varphi_i(X),\\qquad |\\mathrm{supp}(\\varphi_i)|\\le s,$$
  where $X$ are edge variables.
  Then any decision tree $T$ over variables $X\\cup P$ can be transformed into a decision tree $U$ over **only** edge variables $X$ so that:
  1) for any assignment $\\alpha:X\\to\\{0,1\\}$ the value $U(\\alpha)$ coincides with the value $T(\\alpha, P=\\varphi(X))$;
  2) for any branch $\\tau$ of tree $T$, the corresponding branch $\\hat\\tau$ of tree $U$ has depth
     $$\\mathrm{depth}(\\hat\\tau)\\le \\#(X\\text{-queries in }\\tau)+2s\\cdot\\#(P\\text{-queries in }\\tau)\\le (2s+1)\\,\\mathrm{depth}(\\tau).$$
  In particular, if HR Lemma 4.5/Lemma 4.4 requires "decision trees querying edges of the $n\\times n$ grid" of depth $\\le t$, then for flat localEF(s) it is enough to replace the parameter $t$ with $t':=(2s+1)t$ after such unfolding.
- `Proof:`
  For each $p_i$, let $E_i\\subseteq X$ denote the set of edge variables occurring in $\\varphi_i$.
  Since grid has degree $\\le 4$, any fixed set of vertices $S$ is incident to at most $2|S|$ edges, so
  $$|E_i|\\le 2\\,|\\mathrm{supp}(\\varphi_i)|\\le 2s.$$
  Let's build a decision tree $D_i$ over $E_i$ of depth $|E_i|$ that calculates the Boolean function $\\varphi_i$ (for example, we request all variables from $E_i$ in a fixed order and mark the leaves with the value $\\varphi_i$ on the corresponding set).

  Now we define $U$ from $T$ by recursively replacing each query node $p_i$ with the tree $D_i$:
  Each leaf $D_i$, labeled $b\\in\\{0,1\\}$, is redirected to the child of the source node $p_i$ according to the answer $b$.
  Then by induction on the structure of $T$, for any $\\alpha$ the trees $T$ and $U$ compute the same value under the interpretation $p_i:=\\varphi_i(\\alpha)$.

  By depth: replacing one $p_i$-query adds no more than $\\mathrm{depth}(D_i)=|E_i|\\le 2s$ edge-queries along the branch, and $X$-queries are saved.
  From here
  $$\\mathrm{depth}(\\hat\\tau)\\le \\#X(\\tau)+\\sum_{p_i\\in\\mathrm{dom}_P(\\tau)}|E_i|\\le \\#X(\\tau)+2s\\cdot\\#P(\\tau).$$
- `Toy test:` if $p\\leftrightarrow(x_{e_1}\\oplus x_{e_2}\\oplus x_{e_3})$, then $|\\mathrm{supp}(\\varphi)|\\le 6$ and $|E|=3$; unfolding one query $p$ gives a tree of depth 3 on $\\{x_{e_1},x_{e_2},x_{e_3}\\}$.
- `Status:` proven (fixes where exactly in Lemma 4.5 "edgeonly" is used and how to return to it at the cost of a factor $O(s)$ in depth).
- `Barrier check:` r - applicable (purely combinatorial argument about decision trees/support and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, check the parametric mode in HR Lemma 4.5: is it sufficient to preserve conditions of the form $t(\\eta)\\le n_\\eta/16$ and $t\\le s_\\eta\\le n' /32$ after replacing $t\\mapsto (2s+1)t$; if not, record the exact point of failure as a barrier.

### 16.166. Research step: check parameter - how the conditions of HR Lemma 4.5 change after unfolding $t\\mapsto t':=(2s+1)t$

- `Lens:` Trade-off.
- `Statement (Q43.S4-parameter-check-after-unfolding):`
  In HR'22, the proof of Theorem 4.3 uses the parameters of Lemma 4.4/4.5 only through the quantity
  $$t:=\\log M$$
  (the depth of "residual" trees unique to the formula after the common prefix $T_\\eta(\\nu)$).
  Therefore, after unfolding from Section 16.165, which replaces each $P$ query with $\\le 2s$ edge queries and gives
  $$t' := (2s+1)\\,t = (2s+1)\\log M,$$
  the parametric part of HR Lemma 4.5 is preserved *in the same form* when $t\\rightsquigarrow t'$ is replaced:
  - choose $\\ell:=t'$ in Lemma 4.4;
  - set the recursion $n_\\eta:=\\lfloor n_{\\eta-1}/(A_1\\,t'\\,\\log^{c_1} n_{\\eta-1})\\rfloor$ as in HR (PDF p. 19-20), and $s_\\eta:=2^{\\eta-1}\\log N$;
  - the final sufficient verification is reduced to (HR, Proof of Thm. 4.3; PDF p. 19-20)
    $$t'(d)\\le 2^d\\log N + t'\\quad\\text{i}\\quad n_d\\ \\gtrsim\\ \\frac{n}{(\\log^{c_1} n\\cdot t')^d},$$
    which means it's enough to demand
    $$\\log N\\ \\le\\ \\frac{n}{C\\,\\bigl(\\log^{c_1} n\\cdot t'\\bigr)^d}$$
    for a sufficiently large absolute constant $C$.
  In particular, the "price" of flat-extensions in this place is the replacement of $\\log M\\mapsto (2s+1)\\log M$ (that is, the deterioration of the lower bound for length by the factor $(2s+1)^d$ in the denominator of the exponent).
- `Proof:`
  Let's compare it with the parameter block in HR'22 (see. `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`, Proof of Thm. 4.3; PDF p. 19–20):
  (i) HR choose $\\ell=t=\\log M$ and recursion $n_\\eta=\\lfloor n_{\\eta-1}/(A_1\\,t\\,\\log^{c_1} n_{\\eta-1})\\rfloor$, as well as $s_\\eta=2^{\\eta-1}\\log N$ and $t(\\eta)=\\sum_{i\\le\\eta}s_i+\\log M$;
  (ii) the only dependence on $M$ in this block passes through $t=\\log M$ (see the line "We choose $\\ell=t=\\log M$ ..." and the formula $t(\\eta)=\\sum s_i+\\log M$);
  (iii) unfolding from Section 16.165 changes the depth of the "unique part" of the tree by a factor of $2s+1$, that is, it is sufficient to replace $t$ with $t':=(2s+1)t$ in all places where HR uses $t$ as a bound on the depth of the input decision trees in Lemma 4.4.
  All estimates in HR for the probability of failure/union bound use only the quantities $t,\\ell,n_\\eta,s_\\eta$ (and constants), so when replacing $t,\\ell\\rightsquigarrow t'$ we get the same inequalities with $t'$.
  Final check $t(d)\\le n_d/16$ at the end of Proof of Thm. 4.3 (PDF p. 19) also depends on $M$ only through the addition of $+\\log M$, so it becomes $t'(d)\\le n_d/16$ with $+t'$.
- `Toy test:` if $M=\\mathrm{poly}(n)$ and $s=\\mathrm{polylog}(n)$, then $t'=(2s+1)\\log M=\\mathrm{polylog}(n)$, and the replacement $\\log M\\mapsto t'$ only strengthens the polylog factors in the denominator of the exponent.
- `Status:` proven (parametric part; point where flat-extensions are "paid" by the factor $(2s+1)$ over $t$).
- `Barrier check:` r -- applicable (switching lemmas/DT arguments are relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` for Q43, try to reduce "polysize flat localEF(s)  evaluations exist" to HR Lemma 4.5 with replacement $t\\mapsto t'$ and then check that the required local consistency of trees (for evaluation) actually holds in the presence of extension axioms (or fix a specific failure).

### 16.167. Exploratory step: counterexample - naive unfolding $P\\to X$ can violate local branch consistency

- `Lens:` Model stress test.
- `Statement (Q43.S5-check-local-consistency-after-unfolding):`
  Even in the **flat**-mode $p\\leftrightarrow\\varphi(X)$ and with little support $|\\mathrm{supp}(\\varphi)|=O(1)$, a naive replacement of the $P$-query with "complete calculation of $\\varphi$ by edge-variables" can generate a decision tree with **locally inconsistent** branches (in the sense HR'22 Def. 2.5), and therefore such a replacement cannot be directly substituted into the HR definition of evaluation.
- `Counterexample:`
  Consider Tseitin($G_n$) on a $n\\times n$ grid with charges $\\alpha_v=1$ for all vertices (as in HR'22 main case), and choose an internal vertex $v$ of degree 4 with incident edges $e_1,e_2,e_3,e_4$.
  Let's put
  $$\\varphi(X):= (x_{e_1}\\wedge x_{e_2})\\ \\vee\\ (x_{e_3}\\wedge x_{e_4}),$$
  and introduce a flat extension variable $p\\leftrightarrow\\varphi(X)$ (the support of $\\mathrm{supp}(\\varphi)$ consists of $v$ and 4 neighbors, that is, $O(1)$).

  Consider the "naive unfolding" $P\\to X$ as a decision tree $D$ of depth 4, which sequentially requests
  $x_{e_1},x_{e_2},x_{e_3},x_{e_4}$ and in the sheet marks the value $\\varphi$ on the received 4 bits.
  Then $D$ contains a branch
  $$\\tau:\\ x_{e_1}=0,\\ x_{e_2}=0,\\ x_{e_3}=1,\\ x_{e_4}=1,$$
  for which $\\varphi(\\tau)=1$, but the parity at vertex $v$ is equal to
  $$x_{e_1}\\oplus x_{e_2}\\oplus x_{e_3}\\oplus x_{e_4}=0\\ne 1=\\alpha_v.$$
  Since branch $\\tau$ already commits **all** edges incident to $v$, no further assignment can correct the violation of the XOR constraint on $v$.
  This means $\\tau$ is not a locally consistent assignment (HR'22 Def. 2.2), and therefore $D$ is not a locally consistent decision tree (HR'22 Def. 2.5).
- `Toy test:` the parity check in $v$ for the branch $(0,0,1,1)$ gives 0, while the charge $\\alpha_v=1$ requires 1.
- `Status:` counter-example (fixes the risk point in Q43: edgeonly unfolding is obliged to avoid "locally implied" queries or apply aggressive trimming as in HR'22 before Cor. 2.7).
- `Barrier check:` r - applicable (the counterexample is entirely at the local consistency/closure/DT level and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43: formulate and prove a rule for constructing edgeonly decision trees for formulas $\\varphi(X)$ (with $|\\mathrm{supp}(\\varphi)|\\le s$), which guarantees the local consistency of all branches (for example, "do not query locally implied edges", HR'22 p. 7 after Def. 2.5) and estimate the depth in terms of $s$.

### 16.168. Research step: "locally consistent unfolding" for $\\varphi(X)$ - build an edgeonly decision tree without bad branches

- `Lens:` Invariant.
- `Statement (Q43.S6-construct-locally-consistent-unfolding):`
  Let $\\varphi$ be a formula over edge variables $E:=\\mathrm{vars}(\\varphi)\\subseteq X$ on $n\\times n$ grid, and $S:=\\mathrm{supp}(\\varphi)$ be the set of vertices incident to edges from $E$ (so $|S|\\le s$).
  Let $\\alpha$ be a locally consistent partial assignment (HR'22 Def. 2.2) such that
  $$|\\mathrm{supp}(\\alpha)|+|S|\\le n/2.$$
  Then there exists a decision tree $T_{\\varphi,\\alpha}$, which
  1) requests only variables from $E$ and has a depth of $\\le |E|\\le 2|S|\\le 2s$;
  2) is locally consistent (HR'22 Def. 2.5), i.e. each of its branches $\\tau$ gives a locally consistent assignment $\\alpha\\cup\\tau$;
  3) in each leaf, marks the value $\\varphi$ on the branch (that is, $\\varphi\\!\upharpoonright\\!\\tau$ is a $b$-formula, where $b$ is the leaf label).
- `Proof:`
  Note that in a $4$-regular grid each edge gives two incident vertices, and therefore
  $$|E|\\le \\tfrac12\\sum_{v\\in S}\\deg(v)\\le 2|S|.$$
  Let us construct the tree by induction, maintaining the invariant: the current branch $\\tau$ is such that $\\beta:=\\alpha\\cup\\tau$ locally consistent and
  $|\\mathrm{supp}(\\beta)|\\le |\\mathrm{supp}(\\alpha)|+|S|\\le n/2$.
  If $\\varphi\\!\upharpoonright\\!\\tau$ is already a constant, we stop and set the appropriate sheet mark.
  Otherwise, we choose the variable $x_e\\in E\\setminus\\mathrm{dom}(\\tau)$ occurring in $\\varphi\\!\upharpoonright\\!\\tau$.
  By HR'22 Lemma 2.3 (PDF p. 6) there exists $b\\in\\{0.1\\}$ such that $\\beta\\cup\\{x_e\\mapsto b\\}$ locally consistent.
  If such $b$ is unique, then $x_e$ is locally implied by $\\beta$ (HR'22 Def. 2.4), and we **do not branch** on $x_e$ (as in HR'22: "disallow queries ... if x is locally implied", PDF p. 7),
  and add this value to $\\tau$ and continue.
  If $x_e$ is *not* locally implied, then from the existence of at least one $b$ it follows that both branches ($b=0$ and $b=1$) are locally consistent, and we branch $x_e$ into two subtrees.
  In both cases, the invariant is preserved, since we assign only edges incident to vertices from $S$.
  Since at each step we fix a new variable from $E$, the process is completed in $\\le |E|$ steps, and the depth (number of branches) does not exceed $|E|$.
  By construction, all branches are locally consistent and leaves are correctly marked with the $\\varphi$ value on the branch.
- `Toy test:` in the counterexample Section 16.167, after the assignments $x_{e_1}=x_{e_2}=0,\\ x_{e_3}=1$ the edge $e_4$ becomes locally implied (otherwise the XOR constraint at vertex $v$ will be violated), so the branch $x_{e_4}=1$ is cut off and the "bad" branch $(0,0,1,1)$ doesn't appear.
- `Status:` proven (gives the correct pattern "unfolding without bad branches": build/expand trees, prohibiting requests for locally implied edges and trimming by local consistency).
- `Barrier check:` r - applicable (the whole construction is about local consistency/decision trees and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, try to embed $T_{\\varphi,\\alpha}$ into the replacement of $P$-queries inside HR Lemma 4.5, ensuring that functional equivalence and multi-switching remain applicable when replacing $t\\mapsto (2s+1)t$.

### 16.169. Exploratory step: substitution of locally consistent unfolding into $P$ queries (path to using HR Lemma 4.5)

- `Lens:` Equivalence.
- `Statement (Q43.S7-plug-lc-unfolding-into-lemma45):`
  Working in a flat model $p_i\\leftrightarrow\\varphi_i(X)$ with $|\\mathrm{supp}(\\varphi_i)|\\le s$, we can replace any decision tree $T$ over variables $X\\cup P$ with a decision tree $U$ over **only** edge variables $X$, so that:
  1) along any branch $\\tau$ of the tree $U$, the value of each "encountered" $p_i$ is equal to $\\varphi_i\\!\upharpoonright\\!\\tau$ (that is, $U$ implements the calculation of $T$ in the substitution semantics $p_i:=\\varphi_i(X)$);
  2) $U$ can be constructed so that all branches are locally consistent (HR'22 Def. 2.5), using Lemma 2.3 + the "do not query locally implied variables" rule (HR'22, PDF p. 7);
  3) the depth increases by no more than a factor $(2s+1)$: for each branch
     $$\\mathrm{depth}_X(U)\\le \\#X(\\tau_T)+2s\\cdot\\#P(\\tau_T)\\le (2s+1)\\,\\mathrm{depth}(T),$$
     where $\\tau_T$ is the corresponding branch in the original tree $T$.
  Therefore, to use HR multiswitching (Lemma 4.4) inside Lemma 4.5, it is enough to replace the parameter $t=\\log M$ with $t'=(2s+1)\\log M$ *and* build unfolding subtrees that are locally consistent.
- `Proof:`
  We construct $U$ from top to bottom, maintaining the invariant: the current branch gives a locally consistent assignment $\\alpha$ on $X$ with $|\\mathrm{supp}(\\alpha)|\\le n/2$.
  - If the edge variable $x_e$ is requested in $T$, then:
    *if* $x_e$ locally implied by $\\alpha$ (HR'22 Def. 2.4), then we do not branch and continue according to the only locally consistent value;
    otherwise we branch $x_e$ into both branches (both preserve local consistency, otherwise there would be local implication).
  - If an extension variable $p_i$ is requested in $T$, then we insert a subtree $T_{\\varphi_i,\\alpha}$ from Section 16.168 (depth $\\le 2s$), which (i) requests only edges from $\\mathrm{vars}(\\varphi_i)$, (ii) preserves local consistency for each branch, and (iii) in leaf returns $b=\\varphi_i\\!\upharpoonright\\!\\tau$; then we continue constructing the node $p_i$ from the corresponding child (based on the answer $b$).
  Repeating recursively, we get edgeonly $U$ with locally consistent branches.
  The depth estimate is obtained by summation: each $X$-query in $T$ produces a $\\le 1$ edge-level in $U$, and each $P$-query is replaced by a $\\le 2s$ depth subtree.
- `Toy test:` the counterexample of Section 16.167 is eliminated precisely by inserting $T_{\\varphi,\\alpha}$: the branch $(0,0,1,1)$ does not appear because $x_{e_4}$ is locally implied after $x_{e_1}=x_{e_2}=0,\\ x_{e_3}=1$.
- `Status:` proven (local "firmware" Section 16.168 into the HR'22 mechanism: now it remains to check the functional equivalence evaluations after this replacement).
- `Barrier check:` r - applicable (the argument is at the level of local consistency/decision trees and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, check that after such a replacement the required functional equivalence of evaluations is preserved (you may need to weaken/redefine it in a flat localEF(s) context).

### 16.170. Exploratory step: functional equivalence follows from semantic equivalence for locally consistent decision trees

- `Lens:` Equivalence.
- `Statement (Q43.S8-functional-equivalence-after-unfolding):`
  Let $T_1,T_2$ be locally consistent decision trees (HR'22 Def. 2.5) over edge variables Tseitin($G_n$) of depth $\\le n/8$.
  If they evaluate the same Boolean function $f:X\\to\\{0,1\\}$ on all full assignments of $X$, then $T_1$ and $T_2$ are **functionally equivalent** (HR'22 Def. 2.8).
  Consequently, in Q43, after replacing $P$-queries with edge-only locally consistent unfolding (Section 16.169), the functional equivalence of evaluations is preserved automatically: isomorphic formulas define the same function of $X$ (after substituting $p_i:=\\varphi_i(X)$), and hence the corresponding functionally equivalent trees.
- `Proof:`
  Take a branch $\\tau$ of the tree $T_1$ ending with a leaf labeled $b$.
  Then on any complete assignment $\\rho:X\\to\\{0,1\\}$ consistent with $\\tau$, we have $T_1(\\rho)=b$, and therefore, by assumption, $T_2(\\rho)=b$.

  Consider any branch $\\tau'$ of the tree $T_2$ that is pairwise locally consistent with $\\tau$ (HR'22 Def. 2.2).
  Then the union $\\tau\\cup\\tau'$ is a locally consistent partial assignment, and therefore it is extendable to a complete assignment $\\rho$ on $X$ (outside $\\mathrm{closure}(\\mathrm{supp}(\\tau\\cup\\tau'))$ we assign arbitrarily).
  On this $\\rho$ tree $T_2$ passes along the branch $\\tau'$, which means the leaf label $\\tau'$ is equal to $T_2(\\rho)=b$.
  Consequently, **all** branches of $T_2$, pairwise locally consistent with $\\tau$, have label $b$, i.e. "trimmed restriction" $T_2\\!\upharpoonright\\!\\tau$ -- $b$tree.
  Similarly, for any branch $\\tau'$ of the tree $T_2$ we obtain that $T_1\\!\upharpoonright\\!\\tau'$ is the corresponding $b$tree. This is functional equivalence.
- `Toy test:` for isomorphic $\\vee$formulas $((A\\vee B)\\vee C)$ and $(A\\vee(B\\vee C))$ any pair of locally consistent trees that evaluate the same function $A\\vee B\\vee C$ is automatically functionally equivalent by the lemma.
- `Status:` proven (functional equivalence in Q43 boils down to "compute the same function" + local consistency).
- `Barrier check:` r - applicable (the argument is at the level of local consistency/decision trees and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43: after removing the functional-equivalence risk, check that the resulting edge-only trees still satisfy Properties 1-4 of the evaluation definition (and t-common partial decision tree) in step Lemma 4.5.

### 16.171. Exploratory step: "Property 1" in tevaluation is not needed for Lemma 2.13 (we can resolve variables to depth trees $\\le t$)

- `Lens:` Invariant.
- `Statement (Q43.S9-check-evaluation-properties-after-unfolding):`
  The proof of HR'22 Lemma 2.13 (Appendix A.1; PDF p. 50-51) does not use Property 1 from Definition 2.11 (i.e. that *variables* are required to map to depth 1 trees).
  It is enough that (a) all trees are locally consistent and depths $\\le t$, (b) the axioms are 1trees (Property 2), and Properties 3-4 ( and ) plus functional equivalence between rows are satisfied.
  Therefore, in Q43 it is possible, after unfolding, to allow extension variables $p_i$ to be mapped into edge-only trees of depth $O(s)$ (for example, $T_{\\varphi_i,\\alpha}$ from Section 16.168) without breaking the "gatekeeper" of Lemma 2.13.
- `Proof:`
  Let's look at the proof of Lemma 2.13 from HR'22 (PDF p. 50-51): it does row induction and in all cases uses only
  - “axioms are mapped to 1‑trees” (Property 2),
  - connection $T_{\\neg F}$ with $T_F$ (Property 3),
  - that $T_{F\\vee G}$ **represents** $T_F\\vee T_G$ (Property 4),
  - functional equivalence + Lemma 2.9,
  - and Corollary 2.7 (so that $T\\!\upharpoonright\\!\\tau$ was defined at depths $\\le n/16$).

  Nowhere is it required that the tree for the atom $p$ be of depth 1: in "Excluded Middle" they denote $T_p:=\\phi_\\nu(p)$ and work with it only through Properties 3-4; in the remaining rules $p,q,r$ are arbitrary string formulas, and not necessarily atoms.
  Therefore, if we replace Property 1 with the weaker requirement "each atom is mapped to a locally consistent decision tree of depth $\\le t$", then the entire conclusion of Lemma 2.13 remains verbatim.
- `Toy test:` if $p_i\\leftrightarrow\\varphi_i(X)$ and $|\\mathrm{supp}(\\varphi_i)|\\le s$, then after unfolding we can take a tree for $p_i$ equal to $T_{\\varphi_i,\\emptyset}$ of depth $\\le 2s$ (Section 16.168); under the condition $2s\\le t\\le n/16$ Lemma 2.13 applies without modification.
- `Status:` proven (closes "Property 1 check": after unfolding there is no need to maintain depth 1 for extension variables).
- `Barrier check:` r - applicable (the argument is entirely about local consistency/decision trees and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, check the rest of the "evaluation properties" in step Lemma 4.5: that the constructed edgeonly trees indeed produce $t$common partial decision trees and satisfy Property 4 (representation) for formulas after unfolding.

### 16.172. Research step: unfolding does not break the common partial decision tree and Property 4 (representation) - invariance under functional equivalence

- `Lens:` Equivalence.
- `Statement (Q43.S10-common-partial-tree-after-unfolding):`
  Let $T_1,\\dots,T_m$ and $T'_1,\\dots,T'_m$ be locally consistent decision trees over edge variables Tseitin($G_n$) of depth $\\le n/8$ such that for all $i$ the trees $T_i$ and $T'_i$ are functionally equivalent (HR'22 Def. 2.8).
  Then:
  1) (**representation is stable**) if decision tree $R$ represents $\\bigvee_{i=1}^m T_i$ (HR'22, paragraph before Def. 2.10), then $R$ also represents $\\bigvee_{i=1}^m T'_i$;
  2) (**common partial tree is stable**) if partial decision tree $S$ is $\\ell$common partial decision tree for $T_1,\\dots,T_m$ (HR'22 Def. 2.10), then the same $S$ is $\\ell$common partial decision tree for $T'_1,\\dots,T'_m$.

  In particular, in Q43, after replacing $P$-queries with edge-only locally consistent unfolding from Section 16.169 (depth $t\\mapsto t':=(2s+1)t$ and semantic equivalence in the sense of substitution $p_i:=\\varphi_i(X)$), check in HR'22 Lemma 4.5 that $T_\\eta(\\nu)$ -- $t'$common partial decision tree and that Property 4 (representation) is satisfied for $\\vee$formulas, transferred without changes (the check goes "along the branches" and uses only btree facts for trimmed restriction).
- `Proof:`
  Key fact: From HR'22 Lemma 2.9 it follows that for any functionally equivalent $T,T'$ and any locally consistent partial assignment $\\alpha$ (in the mode where all trimmed restrictions are defined) the equivalence holds
  $$T\\!\upharpoonright\\!\\alpha\\text{ — $b$‑tree}\\ \\Longleftrightarrow\\ T'\\!\\upharpoonright\\!\\alpha\\text{ — $b$‑tree}.$$

  1) **Stability for representation.**
     Let $R$ represent $\\bigvee_i T_i$.
     Take a branch $\\tau$ of the tree $R$ ending with a leaf labeled $b$.
     - If $b=0$, then by definition of "represents" we have $T_i\\!\\upharpoonright\\!\\tau=0$ for all $i$, which means by the key fact $T'_i\\!\\upharpoonright\\!\\tau=0$ for all $i$.
     - If $b=1$, then by definition of "represents" there is $i$ with $T_i\\!\\upharpoonright\\!\\tau=1$, which means $T'_i\\!\\upharpoonright\\!\\tau=1$.
     This exactly means that $R$ represents $\\bigvee_i T'_i$.

  2) **Stability for $\\ell$common partial decision tree.**
     Let $S$ be a $\\ell$common partial decision tree for $T_1,\\dots,T_m$.
     Then according to HR'22 Def. 2.10 for each $i$ and each branch $\\tau\\in S$ there is a decision tree $S^{(i,\\tau)}$ of depth $\\ell$ such that if $\\widehat S_i$ is obtained from $S$ by substituting $S^{(i,\\tau)}$ into the sheet $\\tau$, then for any branch $\\tau'\\in\\widehat S_i$ ending with leaf $b$, $T_i\\!\\upharpoonright\\!\\tau'=b$ is satisfied.
     Applying the key fact to each such $\\tau'$, we obtain $T'_i\\!\\upharpoonright\\!\\tau'=b$.
     This means that the same witness-trees $S^{(i,\\tau)}$ prove that $S$ is a $\\ell$-common partial decision tree for $T'_1,\\dots,T'_m$.

  Application to Q43: trees obtained by locally consistent unfolding (Section 16.169) evaluate the same function of $X$ (in semantics $p_i:=\\varphi_i(X)$), and therefore by Section 16.170 are automatically functionally equivalent to any other locally consistent edgeonly representation of the same function.
  Consequently, any trees/partial trees built using HR'22 Lemma 4.4 inside Lemma 4.5 for a "naive" edgeonly representation remain correct for locally consistent unfolding, and Property 4 + common partial tree is carried over (with a single board in the depth parameter $t\\mapsto t'$ from Section 16.166).
- `Toy test:` let $T_1$ be a 1-tree for $x_e$, and let $T'_1$ be a depth 2 tree that first asks $x_e$, then a (locally implied) variable, and does not branch; then $T_1$ and $T'_1$ are functionally equivalent, and any $R$ representing $T_1\\vee 0$ automatically represents $T'_1\\vee 0$ by clause (1).
- `Status:` proven (closes the "common partial tree/representation" node in Q43: after unfolding HR Lemma 4.5 can be applied verbatim by replacing $t\\mapsto t'$).
- `Barrier check:` r - applicable (the argument is purely about decision trees/trimmed restriction and is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, formalize how to obtain input family of decision trees of depth $t'=\\mathrm{polylog}(n)$ from polysize flat localEF(s)proof for Lemma 4.5 (or fix why "row induction" does not produce such trees without nesting/global support).

### 16.173. Research step: where exactly edgeonly trees for Lemma 4.5 are "induced" in flat localEF(s) (unique part + locally consistent unfolding)

- `Lens:` Invariant.
- `Statement (Q43.S11-induce-trees-from-proof):`
  Consider the inductive step HR'22 Lemma 4.5 (PDF p. 20) for a fixed string $\\nu$ and level $\\eta$.
  In it, the "input" trees to which the multiswitching lemma (HR'22 Lemma 4.4) is applied have the form
  $$\\bigl\\{\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau\\bigr\\}_i,$$
  where $\\tau$ is the branch $t$common partial decision tree $T_{\\eta-1}(\\nu)$ of depth $\\sum_{j<\\eta}s_j$.

  In flat localEF(s) (variables $P$ with axioms $p_i\\leftrightarrow\\varphi_i(X)$, $|\\mathrm{supp}(\\varphi_i)|\\le s$) these restricted trees can query $P$.
  Then the "induced" edge-only trees for applying HR Lemma 4.4 are obtained **exactly** like this:
  for each $i$ and each branch $\\tau$ we take locally consistent unfolding
  $$U_{i,\\tau}:=\\mathrm{Unfold}_{\\varphi}(\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau)$$
  from Section 16.169, that is, we replace each $P$ query with a subtree $T_{\\varphi_j,\\alpha}$ (with the current $\\alpha$ along the branch), disabling locally implied edge queries.
  Then:
  1) each $U_{i,\\tau}$ is a locally consistent decision tree over **only** edge variables $X$ (HR'22 Def. 2.5);
  2) depth is limited
     $$\\mathrm{depth}(U_{i,\\tau})\\le (2s+1)\\,t=:t',\\qquad t:=\\log M,$$
     since in HR'22 for any branch $\\tau$ the "common part" of length $\\sum_{j<\\eta}s_j$ is already fixed, and only the unique part of the depth $\\le t$ remains (and unfolding multiplies the depth by at most $2s+1$, Section 16.165).

  Therefore, in the proof of Lemma 4.5, one can apply the HR multiswitching lemma (Lemma 4.4) to families $\\{U_{i,\\tau}\\}_i$ with parameter $t'$ instead of $t=\\log M$.
  The rest of the Lemma 4.5 step (constructing $T_\\eta(\\nu)$ and checking Property 4 "representing $\\vee$" along the branches of $\\tau$) goes verbatim, since it only uses the output of Lemma 4.4 for these input trees.
  This is the formal implementation of the point "polysize proof induces the required edgeonly trees of depth $t'$" in Q43.
- `Proof:`
  In HR'22 Lemma 4.5 (PDF p. 20) to a fixed $\\tau\\in T_{\\eta-1}(\\nu)$ apply Lemma 4.4 to trees
  $\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau$ and use that their depth is $\\le t=\\log M$ ("unique part").
  In flat localEF(s) we replace each such tree with $U_{i,\\tau}$ according to Section 16.169.
  By the construction of Section 16.169, branches $U_{i,\\tau}$ are locally consistent and queries are only edge variables, which means $U_{i,\\tau}$ fits HR'22 Lemma 4.4.

  Depth estimation: Section 16.165 shows that unfolding any decision tree of depth $t$ (where each $P$-query is replaced by a tree of depth $\\le 2s$) yields an edge-only tree of depth $\\le(2s+1)t$.
  Applying this to $\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau$ depth $\\le t$, we get $\\mathrm{depth}(U_{i,\\tau})\\le (2s+1)t=t'$.

  Finally, in HR'22, checking Property 4 (and constructing $T_\\eta(\\nu)$) is done **for each** branch of $\\tau$ separately:
  for a fixed $\\tau$ it is Lemma 4.4 that gives the common partial decision tree of depth $s_\\eta$, which represents the disjunction of the trees associated with the disjuncts.
  Therefore, if we substitute the trees $\\{U_{i,\\tau}\\}_i$ in this place (instead of $\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau$), then the entire step of Lemma 4.5 goes through the same form when replacing $t\\mapsto t'$.
- `Toy test:` for $s=1$, each $P$-query is expanded into a tree of depth $\\le 2$, so the tree of the unique part of depth $t=3$ after unfolding has depth $\\le (2\\cdot 1+1)\\cdot 3=9$.
- `Status:` proven (closes "tree induction" in Q43: the exact location in Lemma 4.5 and the explicit construction of input edgeonly trees of depth $t'$ are indicated).
- `Barrier check:` r - applicable (switching/decision trees are relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43 formulate the final corollary level HR Theorem 4.3 for depth$d$ flat localEF(s): how does the lower bound for length/size change when substituting $t'= (2s+1)\\log M$.

### 16.174. Research step: corollary - HR Theorem 4.3 is transferred to depth$d$ flat localEF(s) with replacement $\\log M\\mapsto (2s+1)\\log M$

- `Lens:` Trade-off.
- `Statement (Q43.S12-corollary-thm43-flat-local-ef):`
  Let a flat localEF(s)refutation Tseitin($G_n$) be given on $n\\times n$ grid (odd charges at each vertex, as in HR'22),
  where all extension axioms have the form $p_i\\leftrightarrow\\varphi_i(X)$ with $|\\mathrm{supp}(\\varphi_i)|\\le s$ (flat),
  and each line is a formula for depth $\\le d$ and size $\\le M$.
  Then the number of rows $N$ satisfies the same form of lower bound as HR'22 Theorem 4.3, but with the replacement
  $$\\log M\\ \\rightsquigarrow\\ t':=(2s+1)\\log M,$$
  that is
  $$N\\ \\ge\\ 2^{\\Omega\\left(\\frac{n}{\\bigl((\\log n)^{O(1)}\\,(2s+1)\\,\\log M\\bigr)^{d}}\\right)}.$$
- `Proof:`
  We repeat the proof of HR'22 Theorem 4.3 (see. `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`, Thm. 4.3 + Proof; PDF p. 19-20), changing exactly one place:
  in Lemma 4.4/4.5 instead of "decision trees querying edges ... of depth $t:=\\log M$" we use edgeonly locally consistent depth trees
  $$t':=(2s+1)\\log M.$$

  The correctness of this replacement is ensured by the previous steps:
  - Section 16.169+Section 16.173: restricted unique parts $\\phi^{\\eta-1}_\\nu(F_i)\\!\upharpoonright\\!\\tau$ in Lemma 4.5 are expanded to edgeonly locally consistent trees of depth $\\le t'$;
  - Section 16.166: Proof of Thm parametric block. 4.3 depends on $M$ only through $t=\\log M$, which means all estimates/union bound are transferred from $t\\rightsquigarrow t'$;
  - Section 16.162: having received at the end $t'(d)$evaluation with $t'(d)\\le n_d/16$, we apply the (flat) analogue of HR Lemma 2.13 and find that there can be no refutation.

  Therefore, to avoid a contradiction with Lemma 2.13, the length of $N$ must satisfy the specified exponential lower bound with $\\log M$ replaced by $t'$.
- `Toy test:` for $s=0$ (no extension variables) we have $t'=\\log M$, and the formula coincides with HR'22 Theorem 4.3.
- `Status:` proven (conditional transfer HR'22 of the lower estimate to depth$d$ flat localEF(s), price is the factor $(2s+1)^d$ in the denominator of the exponent).
- `Barrier check:` r - applicable (switching lemmas/decision trees are relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, check "almost tightness": under what modes $s$ and $M$ the lower estimate remains $2^{n^{1-o(1)}}$ and compare with the known upper $2^{O(n)}$ (resolution).

### 16.175. Exploratory step (toy computation): "almost tightness" modes for corollary at $t'=(2s+1)\\log M$

- `Lens:` Invariant.
- `Statement (Q43.S13-tightness-regime):`
  Let the lower bound from Section 16.174 be executed:
  $$N\\ge 2^{\\Omega\\left(\\frac{n}{\\bigl((\\log n)^{C}\\,(2s+1)\\,\\log M\\bigr)^{d}}\\right)}$$
  for some absolute constant $C\\ge 1$.
  Then:
  1) if
     $$d\\cdot\\log\\bigl((\\log n)^{C}(2s+1)\\log M\\bigr)=o(\\log n),\\tag{*}$$
     then the exponent is equal to $n^{1-o(1)}$, that is
     $$N\\ge 2^{n^{1-o(1)}};$$
  2) in particular, if $(2s+1)\\log M\\le \\log^{O(1)}n$ and $d=o(\\log n/\\log\\log n)$, then the condition $(*)$ is satisfied and again $N\\ge 2^{n^{1-o(1)}}$;
  3) for a fixed depth $d=O(1)$ and $(2s+1)\\log M\\le \\log^{O(1)}n$ we obtain $N\\ge 2^{\\Omega(n/\\log^{O(1)}n)}$, which is consistent with the known upper $2^{O(n)}$ (resolution).
- `Toy computing:`
  From $(*)$ it follows
  $$\\bigl((\\log n)^{C}(2s+1)\\log M\\bigr)^d=2^{o(\\log n)}=n^{o(1)}.$$
  Then the exponent is equal to
  $$\\Omega\\Bigl(\\frac{n}{n^{o(1)}}\\Bigr)=n^{1-o(1)}.$$
  Point (2) is a special case, because for $(2s+1)\\log M\\le \\log^{K}n$ we have $\\log((\\log n)^C(2s+1)\\log M)=O(\\log\\log n)$, and therefore
  $d\\cdot O(\\log\\log n)=o(\\log n)$ for $d=o(\\log n/\\log\\log n)$.
- `Status:` checked (explicit criterion when corollary gives $2^{n^{1-o(1)}}$).
- `Barrier check:` r - applicable (this is only an algebra over parameters + the switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43 estimate the "threshold on $s$": at what $s=s(n)$ (at $M=\\mathrm{poly}(n)$ and $d=o(\\log n/\\log\\log n)$) condition $(*)$ ceases to be true.

### 16.176. Exploratory step (toy computation): threshold on $s$ with $M=\\mathrm{poly}(n)$ and $d=o(\\log n/\\log\\log n)$

- `Lens:` Trade-off.
- `Statement (Q43.S14-threshold-in-s):`
  In the mode $M=\\mathrm{poly}(n)$ (that is, $\\log M=O(\\log n)$) and $d=o(\\log n/\\log\\log n)$ the condition $(*)$ from Section 16.175 is equivalent
  $$d\\cdot\\log(2s+1)=o(\\log n).\\tag{**}$$
  In particular, the lower bound from Section 16.174 gives $N\\ge 2^{n^{1-o(1)}}$ for any $s$ such that
  $$\\log s=o(\\log n/d)\\quad\\text{(that is)}\\quad s\\le 2^{o(\\log n/d)}.$$
- `Toy computing:`
  For $\\log M=O(\\log n)$ we have $\\log\\log M=O(\\log\\log n)$, and therefore
  $$\\log\\bigl((\\log n)^C(2s+1)\\log M\\bigr)=\\log(2s+1)+O(\\log\\log n).$$
  Substituting into $(*)$ from Section 16.175 we get
  $$d\\cdot\\log(2s+1)+d\\cdot O(\\log\\log n)=o(\\log n).$$
  But for $d=o(\\log n/\\log\\log n)$ the second term is automatically $o(\\log n)$, so exactly $(**)$ remains.
- `Status:` checked (explicit threshold for $s$ in subcritical depth).
- `Barrier check:` r - applicable (pure parametrics + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, substitute $s=n^{\\varepsilon}$ and write down for which $d$ the exponent in Section 16.174 remains $n^{1-o(1)}$ or at least $n^{\\Omega(1)}$ (where the lower bound is still non-trivial).

### 16.177. Exploratory step (toy computation): mode $s=n^{\\varepsilon}$ - when the bound from Section 16.174 is non-trivial in depth $d$

- `Lens:` Trade-off.
- `Statement (Q43.S15-poly-s-depth-regime):`
  Let $M=\\mathrm{poly}(n)$, $s=n^{\\varepsilon}$ for fixed $\\varepsilon\\in(0,1)$, and apply corollary Section 16.174:
  $$N\\ge 2^{\\Omega\\left(\\frac{n}{\\bigl((\\log n)^{O(1)}\\,(2s+1)\\,\\log M\\bigr)^{d}}\\right)}.$$
  Then the exponent has the order
  $$\\Omega\\Bigl(\\frac{n^{1-\\varepsilon d}}{\\log^{O(d)} n}\\Bigr).\\tag{***}$$
  From here:
  1) (**almost tightness**) $N\\ge 2^{n^{1-o(1)}}$ is possible only with $\\varepsilon d=o(1)$ (i.e. $d=o(1/\\varepsilon)$);
  2) (**non-triviality**) $N\\ge 2^{n^{\\Omega(1)}}$ is preserved for any constant depth $d$ with $\\varepsilon d<1$;
  3) for $d\\ge 1/\\varepsilon$ the exponent in $(***)$ becomes $n^{o(1)}$, and bound ceases to give a superpolynomial lower bound on $N$.
- `Toy computing:`
  For $s=n^{\\varepsilon}$ we have $2s+1=\\Theta(n^{\\varepsilon})$ and for $M=\\mathrm{poly}(n)$ also $\\log M=\\Theta(\\log n)$.
  Then the denominator in Section 16.174 is
  $$\\bigl((\\log n)^{O(1)}(2s+1)\\log M\\bigr)^d\\ =\\ \\bigl(n^{\\varepsilon}\\,\\log^{O(1)}n\\bigr)^d\\ =\\ n^{\\varepsilon d}\\,\\log^{O(d)}n,$$
  and we get $(***)$.
  Points (1)-(3) follow from comparing $n^{1-\\varepsilon d}$ with $n^{1-o(1)}$, $n^{\\Omega(1)}$ and $n^{o(1)}$, respectively.
- `Status:` tested (explicit "depth-threshold" for polynomial flat-extensions).
- `Barrier check:` r - applicable (parameter + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, consider intermediate modes $s=2^{(\\log n)^\\alpha}$ and compare the threshold $d\\log(2s+1)=o(\\log n)$ with $d=o(\\log n/\\log\\log n)$.

### 16.178. Exploratory step (toy computation): mode $s=2^{(\\log n)^\\alpha}$ -- depth threshold $d\\approx \\log^{1-\\alpha}n$

- `Lens:` Trade-off.
- `Statement (Q43.S16-subexp-s-regime):`
  Let $M=\\mathrm{poly}(n)$ and $s=2^{(\\log n)^\\alpha}$ for some $\\alpha>0$.
  Then the exponent in corollary Section 16.174 has the form
  $$\\Omega\\Bigl(\\frac{n\\,2^{-d\\,(\\log n)^\\alpha}}{\\log^{O(d)}n}\\Bigr).\\tag{****}$$
  In particular:
  1) if $0<\\alpha<1$ and $d=o(\\log^{1-\\alpha}n)$, then $N\\ge 2^{n^{1-o(1)}}$;
  2) if $0<\\alpha<1$ and $d=c\\,\\log^{1-\\alpha}n$ for the constant $c\\in(0,1)$, then $N\\ge 2^{n^{1-c-o(1)}}$;
  3) if $\\alpha>1$, then already for $d\\ge 1$ the expression $(****)$ tends to 0, and corollary Section 16.174 ceases to give a superpolynomial lower bound on $N$.
- `Toy computing:`
  For $s=2^{(\\log n)^\\alpha}$ we have $2s+1=2^{(\\log n)^\\alpha+O(1)}$, and for $M=\\mathrm{poly}(n)$ also $\\log M=\\Theta(\\log n)$.
  Then the denominator in Section 16.174 is
  $$\\bigl((\\log n)^{O(1)}(2s+1)\\log M\\bigr)^d\\ =\\ 2^{d(\\log n)^\\alpha}\\cdot\\log^{O(d)}n,$$
  which gives $(****)$.
  Point (1): $d=o(\\log^{1-\\alpha}n)$ implies $d(\\log n)^\\alpha=o(\\log n)$, and also automatically $d=o(\\log n/\\log\\log n)$, so $\\log^{O(d)}n=2^{o(\\log n)}=n^{o(1)}$.
  Point (2): for $d=c\\log^{1-\\alpha}n$ we have $2^{d(\\log n)^\\alpha}=2^{c\\log n}=n^c$, and $\\log^{O(d)}n=2^{o(\\log n)}=n^{o(1)}$.
  Point (3): for $\\alpha>1$ there is already $2^{d(\\log n)^\\alpha}\\gg n$, therefore $n\\,2^{-d(\\log n)^\\alpha}=o(1)$.
- `Status:` checked (explicit "phase transition": for $\\alpha>1$ bound is trivialized already at depth 1).
- `Barrier check:` r - applicable (parameter + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, select the "maximum permissible" growth of $s(n)$ from the condition $d\\log(2s+1)=o(\\log n)$ with $d=\\Theta(\\log n/\\log\\log n)$ (the boundary between the nontrivial and trivial lower bound).

### 16.179. Exploratory step (toy computation): critical depth $d\\asymp \\log n/\\log\\log n$  $s=(\\log n)^{o(1)}$ for "almost tightness"

- `Lens:` Trade-off.
- `Statement (Q43.S17-max-s-critical-depth):`
  In the mode $M=\\mathrm{poly}(n)$ and "critical" depth
  $$d=\\Theta\\left(\\frac{\\log n}{\\log\\log n}\\right),$$
  the condition $(**)$ from Section 16.176 (equivalent to "almost tightness" $N\\ge 2^{n^{1-o(1)}}$) is equivalent
  $$\\log(2s+1)=o(\\log\\log n),$$
  that is
  $$s=2^{o(\\log\\log n)}=(\\log n)^{o(1)}.$$
- `Toy computing:`
  Substitute $d=\\Theta(\\log n/\\log\\log n)$ into $(**)$ from Section 16.176:
  $$d\\log(2s+1)=o(\\log n)\\ \\Longleftrightarrow\\ \\frac{\\log n}{\\log\\log n}\\cdot\\log(2s+1)=o(\\log n)\\ \\Longleftrightarrow\\ \\log(2s+1)=o(\\log\\log n).$$
  Hence $2s+1=2^{o(\\log\\log n)}$ and therefore $s=2^{o(\\log\\log n)}$.
  The equality $2^{o(\\log\\log n)}=(\\log n)^{o(1)}$ follows from $2^{a\\log\\log n}=(\\log n)^a$.
- `Status:` verified (explicit maximum growth of $s(n)$ at critical depth for conservation of $2^{n^{1-o(1)}}$).
- `Barrier check:` r - applicable (pure parametrics + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43 estimate the "non-triviality bound" for $d=\\Theta(\\log n/\\log\\log n)$: if $s=(\\log n)^c$, what exponent $n^{1-\\Theta(1)}$ gives corollary Section 16.174 (instead of $n^{1-o(1)}$).

### 16.180. Exploratory step (toy computation): with $d=\\Theta(\\log n/\\log\\log n)$ and $s=(\\log n)^c$ exponent = $n^{1-\\Theta(1)}$

- `Lens:` Trade-off.
- `Statement (Q43.S18-polylog-s-critical-depth-exponent):`
  Suppose $M=\\mathrm{poly}(n)$ and $s=(\\log n)^c$ for fixed $c\\ge 0$.
  Let the row depth
  $$d=\\left(\\kappa+o(1)\\right)\\frac{\\log n}{\\log\\log n}$$
  for some constant $\\kappa>0$.
  Then the lower bound from Section 16.174 has an exponent of the form
  $$\\Omega\\bigl(n^{1-\\kappa(C+1+c)-o(1)}\\bigr),$$
  where $C=O(1)$ is the absolute constant from the polylog factor $(\\log n)^{O(1)}$ in Section 16.174 (inherited from HR'22 Thm. 4.3).
  In particular, for $\\kappa(C+1+c)<1$ we obtain a nontrivial bound
  $$N\\ge 2^{n^{\\Omega(1)}},$$
  and when $\\kappa(C+1+c)\\ge 1$ this bound ceases to give a superpolynomial lower bound on $N$.
- `Toy computing:`
  In Section 16.174 the estimate is
  $$N\\ge 2^{\\Omega\\left(\\frac{n}{\\bigl((\\log n)^{C}\\,(2s+1)\\,\\log M\\bigr)^{d}}\\right)}$$
  for some fixed $C\\ge 1$.
  For $M=\\mathrm{poly}(n)$ we have $\\log M=\\Theta(\\log n)$, and for $s=(\\log n)^c$ we have $2s+1=\\Theta((\\log n)^c)$.
  Then
  $$((\\log n)^{C}(2s+1)\\log M)^{d}=\\bigl((\\log n)^{C+1+c}\\bigr)^{d}.$$
  Substituting $d=(\\kappa+o(1))\\log n/\\log\\log n$, we get
  $$\\bigl((\\log n)^{C+1+c}\\bigr)^{d}=2^{(\\kappa+o(1))(C+1+c)\\log n}=n^{\\kappa(C+1+c)+o(1)}.$$
  Therefore the exponent is equal to
  $$\\Omega\\Bigl(\\frac{n}{n^{\\kappa(C+1+c)+o(1)}}\\Bigr)=\\Omega\\bigl(n^{1-\\kappa(C+1+c)-o(1)}\\bigr).$$
- `Status:` verified (critical depth turns polylog$s$ into a constant loss to the power of $n$).
- `Barrier check:` r - applicable (pure parametrics + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, extract/fix the explicit constant $C$ (in $(\\log n)^C$) from Proof of HR'22 Thm. 4.3 and compare the threshold $\\kappa<1/(C+1+c)$ with the actual depth range.

### 16.181. Research Step: $C$ to $(\\log n)^C$ from HR'22 Thm. 4.3 = constant $c_1$ from multiswitching (Lemma 4.4)

- `Lens:` Equivalence.
- `Statement (Q43.S19-pin-down-constant-C):`
  In the HR'22 Theorem 4.3 formulation, the polylog factor $(\\log n)^{O(1)}$ can be taken equal to $\\log^{c_1}n$, where $c_1$ is the constant from HR'22 Lemma 4.4 (Multi-switching Lemma).
  Therefore, in corollary Section 16.174 for flat localEF(s) one can consider
  $$C=c_1$$
  (and all other losses are taken into account separately through $t'=(2s+1)\\log M$).
- `Proof/exact link:`
  In HR'22 Lemma 4.4 (PDF p. 19; `../../resources/downloads/hastad_risse_2022_tseitin_grid_revisited.pdf`) the parametric premise contains
  $$\\frac{n}{n'}\\ge A\\,t\\,\\log^{c_1}n.$$
  In Proof of Theorem 4.3 (PDF p. 19-20), they then choose $\\ell=t=\\log M$ and specify the recursion
  $$n_\\eta=\\Bigl\\lfloor\\frac{n_{\\eta-1}}{A_1\\,t\\,\\log^{c_1}n_{\\eta-1}}\\Bigr\\rfloor\\qquad(\\eta\\in[d]).$$
  In other words, the only source of "$(\\log n)^{O(1)}$" in the denominator of the exponent is precisely the factor $\\log^{c_1}n$ from the multiswitching lemma (Lemma 4.4).
- `Toy test:` if in Lemma 4.4 it were possible to take $c_1=4$, then the formula Thm. 4.3 would become with $(\\log n)^4$ (as in Lemma 4.2/Thm. 4.1); in the text of HR'22 $c_1$ is left as "absolute constant".
- `Status:` exact localization of the constant (we use it in Q43 as explicit $C=c_1$).
- `Barrier check:` r - applicable (switching lemmas/decision trees are relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43: in Proof of Lemma 4.4 (Section 7) try to extract an explicit value/upper bound for $c_1$ (or note that the text does not give a numerical value of $c_1$ without re-analyzing the proof).

### 16.182. Exploratory step (exact citation): in HR'22 Lemma 4.4 the constant $c_1$ (in $\\log^{c_1}n$) is not fixed explicitly

- `Lens:` Compression/canonization.
- `Statement (Q43.S20-bound-c1):`
  In HR'22 Lemma 4.4, the constant $c_1$ is introduced only as "absolute constant" and in proof (Section 7.3) it is not output explicitly: the additional overhead in the inversion of the mapping is "absorbed by the constants $c_1$ and $c_2$".
  Therefore, it is impossible to extract the numerical value/upper bound for $c_1$ from the HR'22 text without independently tracking the constants (or replacing the lemma with a source with explicit parameters).
- `Exact link (HR'22, text cache):`
  1) formulation of Lemma 4.4: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2570–2571` (“There are absolute constants A, c1, c2, n0 > 0 … n/n′ ≥ At log^{c1} n”);
  2) proof, Section 7.3: `…:2776–2777` ("the cost is absorbed by the constants c1 and c2") and `…:2787–2790` (“only the index j cannot be absorbed by the constants A, c1 and c2”).
- `Toy test:` search by templates `c1=`/`choose c1` in text cache does not find an explicit choice of $c_1$ (only used as "absolute constant").
- `Status:` exact citation (the attempt to "estimate $c_1$ from the text" rests on implicit constants).
- `Barrier check:` r -- applicable (switching lemmas are relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` either rerun proof Lemma 4.4 with constant tracking and get an explicit $c_1$, or find a source of multiswitching lemma with an explicitly written exponent of $\\log n$.

### 16.183. Research step (proof): PARITY has polynomial-size formulas of depth $O(\\log m/\\log\\log m)$ (removing the "depth" barrier for the XOR line)

- `Lens:` Trade-off.
- `Statement (Q39.S2-parity-depth-loglog):`
  For each $m\\ge 2$ there is a Boolean formula over the basis $\\{\\wedge,\\vee,\\neg\\}$ that calculates $\\mathrm{PARITY}_m(x_1,\\dots,x_m)$, depths
  $$O\\Bigl(\\frac{\\log m}{\\log\\log m}\\Bigr)$$
  and size $\\mathrm{poly}(m)$ (for example, $O(m^2)$).
  Consequently, with depth $d=\\Theta(\\log m/\\log\\log m)$ **the very representation** of the large XOR-linear condition (as a single Frege line) does not rest on "you need $\\Theta(\\log m)$ in depth"; node Q39 remains in the **syntax output** of the XOR step from the previous lines.
- `Proof (construction):`
  1) For $k\\ge 1$ we define the depth-2 DNF parity formula
  $$\\mathrm{PARITY}^{\\mathrm{DNF}}_k(x_1,\\dots,x_k)\\;:=\\;\\bigvee_{S\\subseteq[k],\\ |S|\\text{ odd}}\\ \\Bigl(\\bigwedge_{i\\in S} x_i\\ \\wedge\\ \\bigwedge_{i\\notin S}\\neg x_i\\Bigr).$$
  It computes $\\mathrm{PARITY}_k$ and has size $O(k\\,2^k)$ and depth 2.
  2) Let $b:=\\lceil\\log_2 m\\rceil$. Let us divide $x_1,\\dots,x_m$ into blocks of length $b$ (we will supplement the latter with constants 0).
  Let $y_1,\\dots,y_{\\lceil m/b\\rceil}$ be formulas where $y_j$ is $\\mathrm{PARITY}^{\\mathrm{DNF}}_b$ in the variables of the $j$-th block.
  Then
  $$\\mathrm{PARITY}_m(x)=\\mathrm{PARITY}_{\\lceil m/b\\rceil}(y_1,\\dots,y_{\\lceil m/b\\rceil}).$$
  3) Iteration: repeat the same step for $\\mathrm{PARITY}_{\\lceil m/b\\rceil}$, again grouping the inputs by $b$ and applying $\\mathrm{PARITY}^{\\mathrm{DNF}}_b$ on each block until the number of inputs becomes $\\le b$ (then we end with one $\\mathrm{PARITY}^{\\mathrm{DNF}}_{\\le b}$).

  Depth: each level adds 2, and the number of levels $t$ satisfies $m/b^t\\le b$, i.e.
  $$t\\le \\left\\lceil\\log_b(m/b)\\right\\rceil=O\\Bigl(\\frac{\\log m}{\\log\\log m}\\Bigr),$$
  this means the depth is $\\le 2t+2=O(\\log m/\\log\\log m)$.
  Size: since $2^b\\le 2m$, we have $|\\mathrm{PARITY}^{\\mathrm{DNF}}_b|=O(b\\,2^b)=O(m\\log m)$.
  At the level of $i$ blocks $\\le m/b^{i+1}$, so the contribution of the size
  $$O\\Bigl(\\frac{m}{b^{i+1}}\\cdot m\\log m\\Bigr)=O\\Bigl(\\frac{m^2\\log m}{b^{i+1}}\\Bigr).$$
  Summing the geometric series over $i=0,1,\\dots,t-1$ and taking into account $b=\\Theta(\\log m)$, we obtain the total size $O(m^2)$.
- `Toy test:` for $m=2^{16}$ we have $b=16$ and levels $t=3$ (since $2^{16}/16^3<16$), that is, the depth is $\\le 8$ with a size of $O(m^2)$.
- `Status:` proven (explicit construction of the formula).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` find/fix whether there is a **polynomial boundeddepth Fregeoutput** of a single XORoperation (the addition of two linear forms over $\\mathbb F_2$) at depth $\\Theta(\\log n/\\log\\log n)$, or a known barrier/equivalence with models like $\\mathrm{AC}^0$Frege with MOD2.

### 16.184. Exploratory step (exact citation): GIRS'19 gives boundeddepth output of XORstep (addition of $\\mathbb F_2$equations) for "compact representation" parity

- `Lens:` Equivalence.
- `Statement (Q39.S3-cite-xor-step-bdfrege):`
  Galesi-Itsykson-Riazanov-Sofronova'19 introduces the "compact representation" $\\Phi^a(S,U)$ for the parity equation
  $$\\bigoplus_{i\\in S} x_i = a$$
  with respect to a fixed refinement $U$ of the set $[n]$.
  In Section 4.2 ("Summation of linear equations") they prove that of two such representations relative to **the same** $U$
  one can syntactically derive their sum over $\\mathbb F_2$, i.e. XOR step
  $$\\Phi^a(S,U),\\ \\Phi^b(T,U)\\ \\vdash\\ \\Phi^{a\\oplus b}(S\\triangle T, U)$$
  in boundeddepth Frege with depth $3d+O(1)$ and polynomial (in the size of representations) overhead.
  This gives a positive "XOR-step" fact in the literature (but only in the compact-representation + general refinement mode).
- `Exact link:`
  `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`, p. 11,
  Section 4.2, **Lemma 24**: “Let $U$ be a $(t_1,\\dots,t_d)$‑refinement … there exist a constant $c$ and a derivation
  $\\Phi^a(S,U),\\Phi^b(T,U)\\vdash_{3d+O(1)}\\Phi^{a\\oplus b}(S\\triangle T,U)$ of size at most $c\\cdot|\\Phi^1(\\emptyset,U)|^6$.”
- `Toy test:` for $S=\\{1,2\\}$, $T=\\{2,3\\}$ we obtain $S\\triangle T=\\{1,3\\}$ and precisely $x_1\\oplus x_3=(x_1\\oplus x_2)\\oplus(x_2\\oplus x_3)$.
- `Status:` exact citation (XOR addition of equations is known for compact representation).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable (local fact about bounded-depth Frege-output).
- `Next step:` compare HR'22 "representing parity" (formulas depth $d$, size $M$) with compact-representation $\\Phi^a(S,U)$: is it possible to translate/maintain a single refinement $U$ into bounded-depth Frege for the required intermediate equations without blow-up, or is this where HR's "missing Gauss step" remains.

### 16.185. Exploratory step (toy computation): GIRScompact XORstep gives only quasipoly size in depth mode $\\Theta(\\log m/\\log\\log m)$

- `Lens:` Trade-off.
- `Statement (Q39.S4-compare-hr-vs-girs-repr):`
  If you try to implement "XORstep" in boundeddepth Frege using **GIRS'19 compact representation** $\\Phi^a(S,U)$ and their Lemma 24,
  then with the row depth $D=\\Theta(\\log m/\\log\\log m)$ (where $m$ is the width of the linear equation), only a quasi-polynomial
  upper bound on output size, not $\\mathrm{poly}(m)$.
  Therefore, the presence of Lemma 24 does not in itself close Q39: there remains a gap between "XORstep exists for compactrepresentation" and
  "XOR-step polynomial-size in the required depth mode for natural parity formulas (HR Section 1.2)."
- `Toy calculation (according to GIRS'19 Lemma 20/21/24):`
  In GIRS'19 (p. 10) Lemma 20: If $t_1\\cdots t_d\\ge m$, then there is $(t_1,\\dots,t_d)$refinement $U$ of set $[m]$.
  By Lemma 21 (p. 10), the corresponding compact parity formula has depth $\\le 3d+1$ and size
  $$|\\Phi^1(\\emptyset,U)|\\ \\le\\ \\prod_{i=1}^d 2^{t_i+1}t_i\\ =\\ 2^{d+\\sum_i t_i}\\cdot\\prod_i t_i.$$
  If we want to fit into the depth $D$, then we take $d:=\\lfloor (D-1)/3\\rfloor$.
  To minimize the rough estimate on the size, we can take all $t_i$ the same: $t:=\\lceil m^{1/d}\\rceil$, then $t^d\\ge m$.
  From Lemma 21 we get
  $$|\\Phi^1(\\emptyset,U)|\\ \\le\\ (2^{t+1}t)^d\\ =\\ 2^{O(d\\,t)}.$$
  In the mode $D\\asymp \\log m/\\log\\log m$ we have $d\\asymp \\log m/\\log\\log m$ and
  $$t=m^{1/d}=2^{\\Theta(\\log m/d)}=2^{\\Theta(\\log\\log m)}=\\log^{\\Theta(1)}m,$$
  so $d\\,t=\\log^{\\Theta(1)}m$ and therefore $|\\Phi^1(\\emptyset,U)|=2^{\\log^{\\Theta(1)}m}$ (quasipoly bound).
  Finally, Lemma 24 (p. 11) gives the derivation of an XOR step of size $\\le c\\cdot|\\Phi^1(\\emptyset,U)|^6$, that is, by this estimate it is also quasi-poly for such $D$.
- `Status:` checked (parametric discontinuity: GIRScompact does not give $\\mathrm{poly}(m)$ for $D\\asymp\\log m/\\log\\log m$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` for Q39 we need either (a) another "compact" parity representation compatible with depth $\\Theta(\\log m/\\log\\log m)$ and $\\mathrm{poly}(m)$-size, for which XOR-step is derived, or (b) a barrier/negative result that XOR-step cannot be poly-size in this depth mode.

### 16.186. Research step (proof): Hastad'20 Thm. 6.5 + XOR-framework  "universal poly XOR-step" is excluded only when $d=o(\\log n/\\log\\log n)$

- `Lens:` Model stress test.
- `Statement (Q39.S5-lb-xor-step-hastad20):`
  Let $d\\le 59\\,\\frac{\\log n}{\\log\\log n}$ (as in Hastad'20, Thm. 6.5) and consider Tseitin(Grid$$) with an odd sum of charges.
  If there were a procedure that for each XOR step occurring in a standard Gaussian/column-summing framework (summing $\\mathbb F_2$ equations at region boundaries),
  built a depth-$d$ Frege-output of this step of size $\\mathrm{poly}(n)$, then there would be a depth-$d$ Frege-output Tseitin(Grid$_n$) of size $\\mathrm{poly}(n)$.
  Comparing with Hastad'20 Thm. 6.5 (any depth$d$ refutation has size $\\ge 2^{\\Omega(n^{1/(58(d+1))})}$) we obtain a contradiction **only in those $d$ regimes where this lower estimate is superpolynomial** (i.e. $n^{1/(58(d+1))}=\\omega(\\log n)$, equivalent $d=o(\\log n/\\log\\log n)$).
  In mode $d=\\Theta(\\log n/\\log\\log n)$ itself is Thm. 6.5 does not prohibit polynomial-size (see counterexample-check Section 16.187).
- `Proof:`
  1) (Lower estimate.) According to Hastad'20, Thm. 6.5 (`../../resources/downloads/hastad_2020_small_depth_frege_tseitin_grids.pdf`, p. 17 in text pdftotext)
  for $d\\le 59\\,\\frac{\\log n}{\\log\\log n}$ any depth-$d$ Frege-refutation Tseitin(Grid$_n$) has the size
  $$\\ge 2^{\\Omega(n^{1/(58(d+1))})}.$$
  2) (Framework for XOR-summation.) In Gaussian/column-summing reasoning, the contradiction $0=1$ is obtained as $\\mathbb F_2$-linear combination of vertex equations
  (the sum of all vertex equations gives $0=\\bigoplus_v \\chi(v)=1$).
  Any such output can be decomposed into $T=\\mathrm{poly}(n)$ local XOR steps of the form
  $$E(S_1,b_1),\\ E(S_2,b_2)\\ \\vdash\\ E(S_1\\triangle S_2,\\ b_1\\oplus b_2)$$
  (see the reduction "XOR step  3-vertex Tseitin" in Section 16.126).
  3) (Glueing.) If each of these $T$ steps has a depth$d$ Fregeoutput of size $\\mathrm{poly}(n)$, then their concatenation gives a depth$d$ refutation of size $T\\cdot\\mathrm{poly}(n)=\\mathrm{poly}(n)$.
  4) (When a contradiction arises.) Concatenation gives a refutation of size $\\mathrm{poly}(n)$, which contradicts point (1) **only if**
  $$2^{\\Omega(n^{1/(58(d+1))})}\\ \\text{superpolynomial in }n.$$
  In this case, there is indeed a "bad step" in the size of the XOR framework
  $$2^{\\Omega(n^{1/(58(d+1))})}/\\mathrm{poly}(n).$$
- `Toy test:` if $d=o(\\log n/\\log\\log n)$, then $n^{1/(58(d+1))}=\\omega(\\log n)$ and the lower bound in (1) is superpolynomial; means "universal poly XORstep" is impossible in this depthmode.
- `Status:` proven (correct formulation: the argument gives a barrier only in the mode $d=o(\\log n/\\log\\log n)$).
- `Barrier check:` r -- applicable (LB Hastad'20 is relativized through the switching lemma), NP -- not applicable, alg -- not applicable.
- `Next step:` for Q39, clarify the class of "XOR framework steps": find whether it is possible to keep a special representation form (general partition/blocks) so that *all* steps fall into the easy mode of Section 16.130 without a base change, or prove that this is impossible.

### 16.187. Exploratory step (counterexample): Thm. 6.5 does not prohibit polynomialsize for $d=\\Theta(\\log n/\\log\\log n)$

- `Lens:` Trade-off.
- `Statement (Q39.S6-block-carcas-or-impossibility):`
  Statement of the form "Hastad'20 Thm. 6.5 prohibits polynomialsize refutation for $d=\\Theta(\\log n/\\log\\log n)$" is incorrect:
  for $d=(\\kappa+o(1))\\frac{\\log n}{\\log\\log n}$ is the lower bound for Thm. 6.5 gives only
  $$\\mathrm{size}\\ \\ge\\ 2^{\\Omega(\\log^{1/(58\\kappa)}n)}=n^{o(1)},$$
  which is compatible with polynomialsize.
  Therefore from Thm. 6.5 cannot be deduced that "universal poly XORstep" is impossible at the *critical* depth; we need a structural argument about basechange/blocks.
- `Toy computing:`
  Let's substitute $d=(\\kappa+o(1))\\frac{\\log n}{\\log\\log n}$ into the exponent Thm. 6.5:
  $$n^{1/(58(d+1))}=\\exp\\Bigl(\\frac{\\log n}{58(d+1)}\\Bigr)=\\exp\\Bigl(\\Theta\\bigl(\\tfrac{\\log\\log n}{58\\kappa}\\bigr)\\Bigr)=\\log^{\\Theta(1)}n.$$
  Hence $2^{\\Omega(n^{1/(58(d+1))})}=2^{\\Omega(\\log^{\\Theta(1)}n)}=n^{o(1)}\\le n$ (for example, for $\\kappa\\ge 1/58$).
  Therefore, the presence of a refutation of size $n^{10}$ at such a depth would **not** contradict Thm. 6.5.
- `Status:` counterexample check (clarifies where exactly "LB  heavy XOR step" works).
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` for Q39: either find a real "hard" XOR step (where a base change between incompatible block splits is inevitable), or construct a sequence of block splits in which all steps remain in the easy mode Section 16.130.

### 16.188. Research step (exact citation): in HR'22 single switching lemma the polylog exponent is fixed (=4), and in the multi-layer the new "non-absorbable" price is only $M^{s/\\ell}$

- `Lens:` Equivalence.
- `Statement (Q43.S21-cite-log4-and-Mfactor):`
  In HR'22, the only *explicitly fixed* polylog exponent in the switching framework is 4 (Lemma 4.2: premise $n/n'\\ge A\\,t\\,\\log^4 n$ and tail $(A t\\log^4 n'/(n/n'))^{s/64}$).
  For multiswitching (Lemma 4.4) in Proof/Section 7.3, the authors explicitly state that from the "additional information" compared to the standard switching case, **only** the index $j\\in[M]$ is "not absorbed" by absolute constants and it is this that generates the multiplier $M^{s/\\ell}$.
  Therefore, to make the exponent $c_1$ explicit in Lemma 4.4, it is enough to track only the places where in Section 7.3 "absorbed by $c_1,c_2$" (for example, identifying additional chosen centers at a distance of 1), and not reassemble the entire singleswitching (where the exponent is already equal to 4).
- `Exact link (HR'22, text cache):`
  1) Lemma 4.2 (Switching Lemma): `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:950–961`.
  2) Proof of Lemma 4.4, Section 7.3 (what exactly does $M^{s/\\ell}$ give and what is "absorbed"): `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2774–2777` and `…:2787–2790`.
- `Toy test:` checking by text cache: in (1) it really costs $\\log^4$, and in (2) the only "non-absorbed" contribution is highlighted verbatim - the index $j$, which generates $M^{s/\\ell}$.
- `Status:` exact citation (localization of sources of explicit/implicit constants in HR'22).
- `Barrier check:` r - applicable (switching/encoding arguments are relativized), NP - not applicable, alg - not applicable.
- `Next step:` for Q43, check that "identity of additional chosen centers" from Section 7.3 actually fits into the previous $b\\log\\Delta$ term (as in Lemma 6.9) and does not require increasing the exponent of $\\log n$ beyond 4; otherwise, write an explicit upper bound on $c_1$ (albeit a rough one).

### 16.189. Research step (toy computation): additional. identification of chosen centers in multiswitching gives a multiplier $(n/n')^{O(s)}$ and affects only $c_2$ (and not $\\log^4$)

- `Lens:` Trade-off.
- `Statement (Q43.S22-check-c1-vs-log4):`
  HR'22 Proof of Lemma 4.4 (Multi-switching) states that to restore "additional chosen centers" at a distance of $\\le1$ from new exposed centers, read $\\le\\log\\Delta$ bits per center and such centers "at most linear in $s$".
  Therefore, all this contribution provides only an additional multiplier
  $$2^{O(s\\log\\Delta)}=\\Delta^{O(s)}=(n/n')^{O(s)}$$
  in encoding (with $\\Delta=\\Theta(n/n')$).
  Such a factor is naturally "hidden" in the constant $c_2$ in the tail of Lemma 4.4 of the form
  $$(At\\,\\log^{c_1}n\\,/(n/n'))^{s/c_2},$$
  those. only changes the coefficient of $\\log(n/n')$ in the exponential, but **does not generate** a new polylog exponent beyond $\\log^4$ from single-switching (Lemma 4.2).
- `Exact link (HR'22, text cache):` `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2774–2777`.
- `Toy test:` $\\log\\Delta$ bits per center and $O(s)$ centers  $O(s\\log\\Delta)$ bits  $2^{O(s\\log\\Delta)}=\\Delta^{O(s)}$.
- `Status:` toy computation (locals what exactly can "inflate" only $c_2$, but not the exponent of $\\log n$).
- `Barrier check:` r -- applicable (the entire encoding evaluation is relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` if you need a *numerical* $c_2$, evaluate the constant in "linear in $s$" for the number of such centers from the common partial decision tree construction (HR'22 Section 7.2) and substitute it into the encoding.

### 16.190. Exploratory step (toy computation): explicit constant in "linear in $s$" for additional chosen centers in HR'22 Lemma 4.4 (<= $2s$)

- `Lens:` Invariant.
- `Statement (Q43.S23-bound-linear-centers):`
  In HR'22 (Lemma 4.4 / Section 7.2-Section 7.3) the number of chosen centers $v$, for which in Section 7.3 you need to "recover the chosen centers $v$ at distance at most 1 from the newly exposed chosen centers", you can take not just "$O(s)$", but **explicitly** $\\le 2s$ for a branch of depth $s$ in the common partial decision tree.
  Consequently, the corresponding identification cost is upper bounded by $\\le 2s\\log\\Delta$ bits.
- `Proof (charge upon requests):`
  Let us take a fixed branch $\\tau$ common partial decision tree $T$ of depth $s$.
  By construction (HR'22 Section 7.2), at each round for long branch $\\lambda^j$ the set $S_{\\lambda^j}$ is introduced and $T$ is expanded with the queries "all variables incident to $S_{\\lambda^j}$".
  Therefore, for each chosen center $v\\in\\bigcup_j S_{\\lambda^j}$ there is at least one request for a variable on the branch $\\tau$ incident to $v$.
  For each such $v$, we select the **first** (in order by $\\tau$) request for a variable incident to $v$.
  But each variable $y_P$ corresponds to a chosen path $P$ connecting **two** chosen centers (HR'22 Section 3), i.e. one request can be incident to no more than two chosen centers.
  This means that the mapping $v\\mapsto$ "first incident query" is $\\le2$-to-$1$, and
  $$\\Bigl|\\bigcup_j S_{\\lambda^j}\\Bigr|\\le 2\\cdot |\\text{queries on }\\tau|=2s.$$
  Hence the identification price is $\\le (2s)\\log\\Delta$ bits.
- `Exact link (HR'22, text cache):`
  1) Definition of $S_{\\lambda^j}$ and "querying all variables incident to $S_{\\lambda^j}$": `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2724–2729`.
  2) The place where it says "linear in $s$": `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2774–2777`.
  3) "chosen path connects two chosen centers" and input $y_P$: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:733–735`.
- `Toy test:` with $s$ queries one can reach $2s$ distinct chosen centers (each query concerns two "new" centers), so the constant 2 is optimal for such a count.
- `Status:` toy computation (explicit constant for hidden "linear in $s$").
- `InfoGain:` 1.
- `Barrier check:` r -- applicable (combinatorial encoding argument is relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` substitute $2s\\log\\Delta$ into the "absorbed by $c_2$" estimate in the proof of Lemma 4.4 (Section 7.3) and write down the rough numerical $c_2$ (taking into account the base $s/64$ from singleswitching).

### 16.191. Exploratory step (toy computation): rough explicit $c_2$ for HR'22 Lemma 4.4 from bound $|\\bigcup_j S_{\\lambda^j}|\\le 2s$

- `Lens:` Trade-off.
- `Statement (Q43.S24-derive-numeric-c2):`
  If in the proof-scheme HR'22 Lemma 4.4 (Multi-switching) we use the same "charge by stages" as in single-switching (Lemma 4.2 through Lemma 6.8-6.9), then we can take **$c_2=64$** (i.e. the same denominator as in the tail $(\\cdot)^{s/64}$), and the contribution of "additional chosen centers" from Section 7.3 only inflates the polylog part: roughly $c_1\\le 132$ is sufficient.
- `Output (as in Lemma 6.8-6.9, with substitution 16.190):`
  1) In single-switching we have $a\\ge s/64$ (HR'22 Lemma 6.8) and an estimate of the number of bad-constraints in terms of $a\\log t+b\\log\\Delta+O(s)$ bits (HR'22 Lemma 6.9), where $b\\le 3a$ (Lemma 6.8), which gives $\\log^{4a}$ and the tail $(At\\,\\log^4(\\cdot)/(n/n'))^{s/64}$ (Lemma 4.2).
  2) In multiswitching, you additionally need to identify chosen centers from $\\bigcup_j S_{\\lambda^j}$; according to Section 16.190 there are no more than $2s$, which means that the contribution to encoding does not exceed $2s\\log\\Delta$ bits.
  3) Charge Lemma 6.8 gives $s\\le 64a$, so $2s\\le 128a$. Therefore, we can simply increase the "$b$-part" by $128a$ and get a rough estimate of $a+b\\le a+(3a+128a)=132a$, i.e. replace $\\log^4$ with $\\log^{132}$, keeping the denominator 64 in the exponent.
- `Toy test:` arithmetic: $a\\ge s/64\\Rightarrow 2s\\le 128a$; for $b\\le 3a$ we get $a+b+128a\\le 132a$.
- `Status:` toy computation (explicit, albeit crude, upper on constants).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (switching/encoding is relativized), NP - not applicable, alg - not applicable.
- `Next step:` clarify whether the "additional chosen centers" from Section 7.3 can really be charged into the same $b\\log\\Delta$-term with coefficient $O(1)$ (then $c_1$ can remain $\\approx 4$), and separately check the contribution of "differences in values" (also declared as absorbed).

### 16.192. Research step (exact citation): HR'22 Section 7.3 - "additional chosen centers" and "differences in values" are absorbed; only the index $j$ gives the factor $M^{s/\\ell}$

- `Lens:` Trade-off.
- `Statement (Q43.S25-tighten-c1-charge):`
  The proof of Multi-switching Lemma 4.4 (HR'22) in Section 7.3 explicitly lists the additional data read at each round of inversion:
  (i) index $j\\in[M]$ (log $M$ bits),
  (ii) the identity of additional chosen centers at a distance of $\\le 1$ from the new exposed centers (log $\\Delta$ bits per center),
  (iii) "differences in values" between responses in trees $T^j$ and $T$.
  HR'22 directly state that **only** (i) is not absorbed by the constants $A,c_1,c_2$ and it is this that generates the factor $M^{s/\\ell}$ in the estimate of Lemma 4.4; points (ii)-(iii) are absorbed by constants.
- `Exact link (HR'22, text cache):`
  1) (ii) + “absorbed by $c_1,c_2$”: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2774–2777`.
  2) (iii) “differences in values”: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2778–2783`.
  3) "only index $j$ cannot be absorbed"  factor $M^{s/\\ell}$: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2787–2790`.
- `Toy test:` verified by text cache that statements (ii)-(iii) and the conclusion "only the index $j$" are indeed written in Section 7.3.
- `Status:` exact link (closes the subparagraph "differences in values absorbed"; all that remains is to unpack "absorbed" into explicit constants for $c_1$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (encoding argument is relativized), NP - not applicable, alg - not applicable.
- `Next step:` write out an explicit upper bound on the number of "differences in values" bits per round (in terms of $s$ or $a,b$ from Lemma 6.9) and thereby separate out the contribution that changes only $A$ (and not $c_1$).

### 16.193. Research step (toy computation): "differences in values" in HR'22 Section 7.3 cost <= 1 bit per request and only change the constant $A$

- `Lens:` Invariant.
- `Statement (Q43.S26-bound-diff-values-bits):`
  In the inversion scheme Multi-switching Lemma 4.4 (HR'22, Section 7.3), the additional information "differences in values" is encoded <= 1 bit for each Boolean variable requested on the considered branch of the common decision tree $T$; therefore, on a branch of depth $s$ the total cost <= $s$ bits.
  Since in singleswitching we have $a\\ge s/64$ (HR'22 Lemma 6.8), then $s\\le 64a$ and the contribution <= $64a$ bits only multiplies the encoding counter by $2^{64a}=(2^{64})^a$, i.e. is absorbed by an increase in the constant $A$ and **does not** change $c_1,c_2$.
- `Proof (bit counting):`
  At each round of HR'22 they read "difference in values of variables queried in the decision tree $T^j$ and the same variables in the common decision tree $T$" (Section 7.3).
  For each such variable, the value in $T^j$ and in $T$ are two bits, which means their difference is determined by one bit (XOR).
  On a fixed branch $\\tau$ of the common decision tree $T$ of depth $s$, exactly $s$ variables are requested, so even in the worst case, <= $s$ bits are enough to set the differences for all these requests (by round, this is simply a split of the requests of the $\\tau$ branch).
  Using $s\\le 64a$ (Lemma 6.8), we get <= $64a$ bits over Lemma 6.9 encoding; this gives a factor $2^{64a}=(2^{64})^a$, which is absorbed by the substitution $A\\leftarrow 2^{64}A$ in the final probability estimate.
- `Toy test:` on the branch of $s$ Boolean queries, the difference vector can be arbitrary in $\\{0,1\\}^s$, so that linear in $s$ upper (and "1 bit per query") is asymptotically exact.
- `Status:` toy computation (explicit bound on "differences in values", separating the contribution to $A$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (the encoding count is relativized), NP - not applicable, alg - not applicable.
- `Next step:` also "inflate" point (ii) about additional chosen centers into explicit constants, but try to charge it into the same $b\\log\\Delta$-term without increasing the logarithm exponent (to keep $c_1\\approx 4$).

### 16.194. Exploratory step (toy computation): "additional chosen centers" in HR'22 Section 7.3 give <= $5a$ centers (not <= $2s$), improving the rough bound by $c_1$

- `Lens:` Compression/canonization.
- `Statement (Q43.S27-charge-centers-into-b):`
  In HR'22 Section 7.3 (Multi-switching Lemma 4.4), additional information (ii) "identity of additional chosen centers" can be limited not through the depth of the $s$ common tree branch, but through the $a$ parameter from singleswitching encoding (HR'22 Lemma 6.8): on the entire depth $s$ branch it is enough to restore no more than $5a$ chosen centers from the union $S_{\\lambda^j}$ by rounds $j$.
  Therefore, the cost of item (ii) is <= $5a\\log\\Delta$ bits, and the rough transition "<=$2s$ centers  $c_1\\le 132$" (Section 16.191) can be replaced by "<=$5a$ centers  $b$ effectively changes to $b+5a\\le 8a$", i.e. $c_1$ can be taken of order 9 (in the same estimation scheme).

- `Proof (counting centers):`
  In HR'22 Section 7.2, the set $S_{\\lambda^j}$ is defined as chosen centers at a distance <=1 from *new* exposed chosen centers on the long branch $\\lambda^j$ (see `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2720–2726`).
  Let
  $$U_j:=(S(\\lambda^j,\\sigma)\\setminus S(\\tau,\\sigma))\\cap C_\\sigma$$
  - these "newly exposed chosen centers". Then, by definition, $S_{\\lambda^j}\\subseteq N_{\\le 1}(U_j)$, where the neighborhood is taken by "adjacent sub-squares" (HR'22: "neighbors ... in adjacent sub-squares"; `…:1573–1574`), and therefore on the lattice of sub-squares
  $$|S_{\\lambda^j}|\\le |U_j|+4|U_j|=5|U_j|.$$
  Further, each new exposed chosen center from $U_j$ appears in stage $j$ as the associated center of some variable on the corresponding 1branch (this is exactly what $a_j$ is considered in HR'22 Lemma 6.8; `…:2078–2086`), whence $|U_j|\\le a_j$.
  Summing up by rounds,
  $$\\Bigl|\\bigcup_j S_{\\lambda^j}\\Bigr|\\le \\sum_j |S_{\\lambda^j}|\\le 5\\sum_j a_j=5a.$$
  In Section 7.3 HR'22 they indicate that <=$\\log\\Delta$ bits are read to restore each such chosen center (`…:2774–2777`), which means the total budget for (ii) <= $5a\\log\\Delta$ bits.

- `Toy test:` worst-case on the lattice: if $U_j$ is a set of pairwise "spaced apart" new exposed centers, then their neighborhoods almost do not intersect and $|S_{\\lambda^j}|\\approx 5|U_j|$, i.e. the constant 5 is exact in order.
- `Status:` toy computation (improved calculation of "additional chosen centers" via $a$, without factor 64).
- `InfoGain:` 2.
- `Barrier check:` r - applicable (encoding arguments are relativized), NP - not applicable, alg - not applicable.
- `Next step:` try to strengthen $|U_j|\\le a_j$ to "$S_{\\lambda^j}$ is already in $b$ from Lemma 6.9" (i.e. show that (ii) does not increase the polylog exponent at all), or find the exact point where this is impossible.

### 16.195. Research step (proof): (ii) "identity of additional chosen centers" in HR'22 Section 7.3 does not increase the polylogscore - it is already covered by $b\\log\\Delta$ from Lemma 6.9

- `Lens:` Compression/canonization.
- `Statement (Q43.S28-centers-already-in-b):`
  In the proof of HR'22 Lemma 4.4 (Multi-switching, Section 7.3), the additional clause (ii) "identity of additional chosen centers" for sets $S_{\\lambda^j}$ can be charged into the same $b\\log\\Delta$-term as in single-switching Lemma 6.9: centers $v\\in S_{\\lambda^j}$ are already restored by standard inversion as "unexposed neighbors" of new exposed chosen centers, and cases where $\\log\\Delta$ is needed coincide with "other disappearing centers" calculated in $b$.

- `Proof (according to HR'22 text):`
  In the $j$ multi-switching round, a long branch $\\lambda^j$ is given and
  $$U:=(S(\\lambda^j,\\sigma)\\setminus S(\\tau,\\sigma))\\cap C_\\sigma$$
  -- set of "newly exposed chosen centers" (HR'22: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2724–2729`).
  By definition, $S_{\\lambda^j}$ each $v\\in S_{\\lambda^j}$ lies in a sub-square adjacent (in $n'\\times n'$-lattice) to some $u\\in U$.
  Since when constructing $T^j$ "maintain the same invariants as in Invariants 6.1" (HR'22: `…:2698–2699`), then for each exposed chosen center $u$ on branch $\\lambda^j$ **all** incident variables $y_P$ are requested (Invariant 6.1(5); `…:1858–1861`).
  In particular, the variable of the selected path between $u$ and the neighboring $v$ is requested, and the information piece $\\{u,v\\}$ is present in the restored information set.
  Exactly such situations (edge/non-edge between chosen exposed center $u$ and unexposed chosen center $v$) are analyzed in the proof of Lemma 6.9: Case 1-3 when recovering $I_j$ (`…:2518–2534`).
  In Case 1 $v$ is restored later, in Case 3 - free of charge as alive chosen center, and in Case 2 $v$ is identified for $\\log\\Delta$ bits and is **not** an associated center (according to Property 2, Definition 6.2), that is, it refers to "other disappearing centers", paid for $b\\log\\Delta$ (`…:2531–2534`, `…:2547–2548`).
  Therefore, (ii) does not require adding a new $\\log\\Delta$-budget on top of Lemma 6.9 and does not increase the polylog-score compared to single-switching (except for a separate factor at index $j\\in[M]$).

- `Toy test:` locally on the lattice, each new exposed chosen center $u$ has <=4 neighboring chosen centers; according to Invariant 6.1(5), they inevitably appear as the second ends of queried variables, and Lemma 6.9 Case 1-3 provides a ready-made scheme for their recovery without a new polylog.
- `Status:` proven (at the level of the HR'22 inversion scheme; point (ii) does not increase the polylog indicator).
- `InfoGain:` 2.
- `Barrier check:` r - applicable (encoding arguments are relativized), NP - not applicable, alg - not applicable.
- `Next step:` update Section 16.191-Section 16.194: remove the "$+5a$" addition as mandatory for $c_1$, fix $c_1\\approx 4$ (and separately remove the only non-absorbable contribution $\\log M$), or specify the exact place where "forgotten answers" break the forward carry of Cases 1-3.

### 16.196. Research step (proof): in HR'22 Lemma 4.4 you can take $c_1=4$; non-absorbable contribution Section 7.3 - only index $j$ (gives factor $M^{s/\\ell}$)

- `Lens:` Compression/canonization.
- `Statement (Q43.S29-propagate-c1-back-to-4):`
  In the probabilistic estimate HR'22 Lemma 4.4 (Multi-switching), the indicator $c_1$ for $\\log^{c_1}n$ can be chosen equal to $4$ (as in single-switching Lemma 4.2), i.e. without an increase in the polylog indicator compared to single switching.
  All additional data listed in HR'22 Section 7.3, except for the index $j\\in[M]$, is absorbed by the constants $A,c_2$; the only unabsorbed contribution comes from the factor $M^{s/\\ell}$ (equivalent to reading $(s/\\ell)\\log M$ bits).

- `Proof (reduction to single-switching):`
  HR'22 Section 7.3 lists additional data (i)-(iii) at each inversion round; Moreover, the text directly states that **only** (i) "cannot be absorbed by the constants $A,c_1,c_2$" and it is this that generates the factor $M^{s/\\ell}$ (see. `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2774–2790`).
  For (iii) "differences in values", <= $s$ bits per branch of depth $s$ are sufficient, which means that for $a\\ge s/64$ (HR'22 Lemma 6.8) we have $s\\le 64a$ and this contribution gives the factor $2^{O(a)}$, absorbed by the increase in $A$ (see Section 16.193).
  For (ii) "identity of additional chosen centers" under Section 16.195, there is no need to add a new $\\log\\Delta$budget beyond Lemma 6.9: the corresponding centers are already restored in Cases 1-3 and (in the only place where $\\log\\Delta$ is needed) refer to "other disappearing centers", paid for by the same $b\\log\\Delta$.
  Consequently, in the part responsible for the polylog exponent $\\log^{c_1}n$, multi-switching uses the same single-switching encoding, where $c_1=4$ (Lemma 4.2), and all differences are reduced to the factor $M^{s/\\ell}$ and renormalization $A$.

- `Toy test:` if (ii) or (iii) required increasing $b$ beyond $3a$ or adding a $\\log\\Delta$ term "on top" of Lemma 6.9, this would manifest itself as an increase in the exponent of $\\log n$ under the assumption $n/n'\\ge A t\\log^{c_1}n$; after Section 16.193 and Section 16.195, only (i) remains, giving the factor $M^{s/\\ell}$ without changing $c_1$.
- `Status:` proven (explicit $c_1=4$ is obtained and the only contribution $\\log M$ is isolated).
- `InfoGain:` 2.
- `Barrier check:` r - applicable (switching/encoding is relativized), NP - not applicable, alg - not applicable.
- `Next step:` in corollary estimates for Q43, replace "$(\\log n)^C$ from Thm. 4.3" with explicit $\\log^4 n$, leaving $\\log M$ only in the parameter $t$ (and the factor $M^{s/\\ell}$), and recheck the non-triviality threshold at $d=\\Theta(\\log n/\\log\\log n)$.

### 16.197. Exploratory step (proof): explicit corollary with $\\log^4 n$ for $c_1=4$ and dependence on $M$ only through $t'$ and $M^{s/\\ell}$

- `Lens:` Compression/canonization.
- `Statement (Q43.S30-log4-into-corollary):`
  Let there be a flat localEF(s)refutation Tseitin($G_n$) on $n\\times n$ grid (odd charges, as in HR'22),
  and each line is a formula for depth $\\le d$ and size $\\le M$.
  Then the number of rows $N$ satisfies the explicit lower bound
  $$N\\ \\ge\\ \\exp\\!\\left(\\Omega\\left(\\frac{n}{\\bigl((\\log n)^4\\,(2s+1)\\,\\log M\\bigr)^{d}}\\right)\\right).$$
  Moreover, the dependence on $M$ in the proof passes **only** through $t'=(2s+1)\\log M$ and through the factor $M^{s/\\ell}$ from multiswitching (index $j\\in[M]$); there are no other $\\log M$ contributions to the polylog exponent.
- `Proof:`
  According to Section 16.174 we have corollary HR'22 Thm. 4.3 with the replacement $t=\\log M\\mapsto t'=(2s+1)\\log M$ and the polylog factor $(\\log n)^{O(1)}$.
  According to Section 16.181, this indicator is equal to $\\log^{c_1}n$, where $c_1$ is the constant from HR'22 Lemma 4.4,
  and according to Section 16.196 you can take $c_1=4$ (as in singleswitching).
  Substituting $c_1=4$ into corollary Section 16.174, we obtain the indicated formula with $(\\log n)^4$.

  Dependency on $M$: Proof of Thm parametric block. 4.3 uses $M$ only via $t=\\log M$ (Section 16.166),
  and the only non-absorbable contribution of Section 7.3 HR'22 is the index $j\\in[M]$, giving the factor $M^{s/\\ell}$ (Section 16.196).
  Consequently, after unfolding, the dependence on $M$ goes only through $t'$ and $M^{s/\\ell}$, as stated.
- `Toy test:` at $s=0$ we obtain the initial HR'22 Thm. 4.3 with $(\\log n)^4$ (singleswitching Lemma 4.2).
- `Status:` proven (explicit substitution of $c_1=4$ into corollary).
- `InfoGain:` 1.
- `Barrier check:` r -- applicable (switching/DT arguments are relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` for $M=\\mathrm{poly}(n)$ and $s=(\\log n)^c$, recalculate the exponent at the critical depth $d=(\\kappa+o(1))\\log n/\\log\\log n$ with an explicit constant $4$ (Q43.S31-critical-depth-kappa).

### 16.198. Exploratory step (toy computation): critical depth $d=(\\kappa+o(1))\\log n/\\log\\log n$ at $s=(\\log n)^c$

- `Lens:` Trade-off.
- `Statement (Q43.S31-critical-depth-kappa):`
  Let $M=\\mathrm{poly}(n)$, $s=(\\log n)^c$ for fixed $c\\ge 0$, and
  $$d=\\left(\\kappa+o(1)\\right)\\frac{\\log n}{\\log\\log n}.$$
  Then corollary Section 16.197 gives
  $$N\\ge 2^{\\Omega(n^{1-\\kappa(5+c)-o(1)})}.$$
  In particular, lower bound is nontrivial ($N\\ge 2^{n^{\\Omega(1)}}$) if and only if
  $$\\kappa<\\frac{1}{5+c}.$$
- `Toy computing:`
  In Section 16.197 we have
  $$N\\ge 2^{\\Omega\\left(\\frac{n}{\\bigl((\\log n)^4(2s+1)\\log M\\bigr)^d}\\right)}.$$
  For $M=\\mathrm{poly}(n)$ we obtain $\\log M=\\Theta(\\log n)$, and for $s=(\\log n)^c$ we have $2s+1=\\Theta((\\log n)^c)$.
  Then
  $$\\bigl((\\log n)^4(2s+1)\\log M\\bigr)^d=\\bigl((\\log n)^{5+c}\\bigr)^d.$$
  Substituting $d=(\\kappa+o(1))\\log n/\\log\\log n$, we get
  $$\\bigl((\\log n)^{5+c}\\bigr)^d=2^{(\\kappa+o(1))(5+c)\\log n}=n^{\\kappa(5+c)+o(1)},$$
  and therefore the exponent is equal to $n^{1-\\kappa(5+c)-o(1)}$.
- `Toy test:` for $c=0$, $M=n^2$, $\\kappa=1/6$ we have
  $$\\bigl((\\log n)^5\\bigr)^d=2^{(5/6+o(1))\\log n}=n^{5/6+o(1)},$$
  means $N\\ge 2^{\\Omega(n^{1/6})}$.
- `Status:` verified (explicit $\\kappa$threshold at critical depth with $c_1=4$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (parameter + switching framework is relativized), NP - not applicable, alg - not applicable.
- `Next step:` estimate the contribution of the factor $M^{s/\\ell}$ under the natural choice of $\\ell:=t'=(2s+1)\\log M$ and check whether it remains $2^{\\Theta(1)}$ (Q43.S32-m-factor-ell-constant).

### 16.199. Exploratory step (toy computation): constancy of the factor $M^{s/\\ell}$ for $\\ell=t'$

- `Lens:` Trade-off.
- `Statement (Q43.S32-m-factor-ell-constant):`
  Let $s\\ge 0$, $M>1$ and
  $$\\ell:=t':=(2s+1)\\log M.$$
  Then
  $$M^{s/\\ell}=2^{\\frac{s}{2s+1}}\\le 2^{1/2},$$
  that is, the factor $M^{s/\\ell}$ is an absolute constant and is absorbed into $A$.
- `Toy computing:`
  $$M^{s/\\ell}=2^{\\frac{s}{\\ell}\\cdot\\log M}=2^{\\frac{s}{(2s+1)\\log M}\\cdot\\log M}=2^{\\frac{s}{2s+1}}.$$
  Since $s/(2s+1)\\le 1/2$ for $s\\ge 0$, we obtain $M^{s/\\ell}\\le 2^{1/2}$.
  (When passing to $e^x$ we obtain $M^{s/\\ell}=e^{s/(2s+1)}\\le e^{1/2}$.)
- `Toy test:` for $s=1$, $M=2$ we have $2^{1/3}\\le\\sqrt{2}$.
- `Status:` verified (the factor $M^{s/\\ell}$ is constant for $\\ell=t'$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (pure arithmetic in parameters), NP - not applicable, alg - not applicable.
- `Next step:` check the validity of the choice $\\ell=t'$ in Lemma 4.4/Def. "$\\ell$common" (is there a $\\ell\\le s$ restriction or another) - Q43.S33-ell-admissibility-check.

### 16.200. Exploratory step (exact citation): admissibility of $\\ell=t'$ in Def. 2.10 / Lemma 4.4

- `Lens:` Equivalence.
- `Statement (Q43.S33-ell-admissibility-check):`
  In HR'22 Def. 2.10 and Lemma 4.4 the parameter $\\ell$ is not bounded from above (there are no conditions of the form $\\ell\\le t$ or $\\ell\\le s$);
  This means that the choice of $\\ell=t'$ is admissible at the formulation level (while maintaining the conditions on $t,s$ from Lemma 4.4).
- `Exact citation:`
  Def. 2.10: “for every $T_i$ and branch $\\tau\\in T$ there are decision trees $T^{(i,\\tau)}$ of depth $\\ell$ …”
  without additional conditions on $\\ell$ (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:574–582`).
  Lemma 4.4: parameters $k,M,n',s,t\\in\\mathbb N^+$ with conditions $t\\le s\\le n'/32$ and $\\mathrm{depth}(T_i)\\le t$,
  and $\\ell$ appears only in the requirement "represented by an $\\ell$common partial decision tree of depth $s$"
  and in the factor $M^{s/\\ell}$ (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1073–1084`).
- `Toy test:` with a tree of depth $t$ and a partial tree of depth $0$ Def. 2.10 allows any $\\ell$,
  so the choice of $\\ell>t$ does not cause a contradiction in the definition.
- `Status:` confirmed (there are no restrictions on $\\ell$ in the formulations).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable (quote/wording), NP - not applicable, alg - not applicable.
- `Next step:` check whether the proof of Lemma 4.4 uses the hidden condition $\\ell\\le t$ or $\\ell\\le s$ (Q43.S35-ell-vs-t-constraint).

### 16.201. Exploratory step (toy computation): hidden $\\ell\\le s$ in round counting Lemma 4.4

- `Lens:` Invariant.
- `Statement (Q43.S35-ell-vs-t-constraint):`
  In the proof of Lemma 4.4, the factor $M^{s/\\ell}$ is obtained from "one index $j\\in[M]$ per round"
  (HR’22 §7.3: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2784–2790`).
  This requires an upper bound on the number of rounds along the branch of depth $s$; in Section 7.2 the round ends,
  when $\\ge\\ell/4$ centers are added, and then $T$ is queried for all variables incident to $S_{\\lambda_j}$
  (HR’22 §7.2: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2718–2732`).
  Therefore, without explicit rounding, we get the implicit constraint $\\ell\\le s$ (otherwise the number of rounds
  may be $1$, whereas $s/\\ell<1$).
- `Toy test:` let $s=2$, $t=1$, $\\ell=5$. Each round adds $\\ge\\ell/4>1$ centers and
  incident variables are requested, which means one iteration already gives the depth $\\ge s$ and requires one
  index $j$ (cost $\\log M$). But $s/\\ell=0.4$, and the multiplier $M^{s/\\ell}$ gives $<M$; this is incompatible with
  "one index per round", if you do not introduce an explicit $\\lceil s/\\ell\\rceil$ or the condition $\\ell\\le s$.
- `Status:` counterexample toy to the "no hidden limitation" hypothesis; need explicit clause $\\ell\\le s$
  (or rounding the number of rounds).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable (local proof check), NP - not applicable, alg - not applicable.
- `Next step:` check in the original PDF/proof how the number of rounds is fixed
  (rounding/transition) and is it possible to replace $M^{s/\\ell}$ with $M^{\\lceil s/\\ell\\rceil}$ without changing the rest.

### 16.202. Exploratory step (proof): rounding the number of rounds by depth

- `Lens:` Invariant.
- `Statement (Q43.S36-round-count-from-depth):`
  In Section 7.2, each round adds at least $\\ell$ **new** queries to branch $T$,
  therefore, a prefix of length $s$ on any branch can cross at most $\\lceil s/\\ell\\rceil$ rounds.
  Therefore, "one index $j$ per round" gives the factor $M^{\\lceil s/\\ell\\rceil}$ (for $s<\\ell$ this gives $M$).
- `Proof:`
  In Section 7.2, the round selects a branch $\\lambda$ of length $\\ge\\ell$ in $T^j$ and **expands** $T$ into leaf $\\tau$
  queries for "all variables on $\\lambda$" (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2671–2684`).
  By definition of a decision tree, the internal markup on any branch uses **different** variables
  (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:489–494`),
  and when expanding a sheet, queries to variables locally implied by $\\tau$ are prohibited
  (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:532–535`),
  so $\\lambda$ adds $\\ge\\ell$ new requests to the current branch.
  This means that a prefix of length $s$ can include no more than $\\lceil s/\\ell\\rceil$ rounds
  (each round produces at least $\\ell$ new queries), and the index $j\\in[M]$ is encoded
  no more than $\\lceil s/\\ell\\rceil$ times.
- `Toy test:` $s=2$, $\\ell=5$: the first round already adds $\\ge 5$ requests, so the prefix is of length $2$
  uses $\\le 1$ round; $M^{\\lceil 2/5\\rceil}=M$.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable (local estimate in the proof), NP - not applicable, alg - not applicable.
- `Next step:` check the alternative bound by the number of centers (Q43.S37-round-count-from-centers).

### 16.203. Exploratory step (counterexample): "$\\ge\\ell/4$ centers per round" does not imply $\\le\\lceil 4a/\\ell\\rceil$

- `Lens:` Invariant.
- `Statement (Q43.S37-rounds-via-uj):`
  In Section 7.2, "$\\ge\\ell/4$ centers per round" refers to **all** exposed centers in $S(\\lambda^j,\\sigma)$, not associated centers.
  Therefore, the statement "each round adds $\\ge\\ell/4$ associated centers" (and therefore bound $\\#\\text{rounds}\\le\\lceil 4a/\\ell\\rceil$) is false without additional structure.
  In general, from Lemma 6.5-6.8 it follows only
  $$\\#\\text{rounds}\\le\\Bigl\\lceil\\frac{64a}{\\ell}\\Bigr\\rceil.$$
- `Counterexample (structural break):`
  In Section 7.2, the round ends when "at least $\\ell/4$ centers have been added ... to $S(\\lambda^j,\\sigma)$" (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2718–2722`).
  But at one stage the centers are added as $\\mathrm{supp}(J)\\cup S_J$, and Lemma 6.5 gives the upper bound "at most $4|\\mathrm{supp}(J)|$ centers are added" (ibid.: `…:2013–2022`).
  Next, Lemma 6.8 states $|\\mathrm{supp}(J)|\\le 4a_j$ (ibid.: `…:2081–2086`), so one stage can add up to $16a_j$ centers.
  Therefore, the round can reach the $\\ell/4$ threshold at $a_j\\ge \\ell/64$, so the output $a_j\\ge\\ell/4$ (and bound $\\lceil 4a/\\ell\\rceil$) fails; the correct general upper is $\\lceil 64a/\\ell\\rceil$.
- `Toy test:` a local configuration, where each associated center gives 3 neighboring chosen centers in $\\mathrm{supp}(J)$, and each of them has 3 more new neighboring chosen centers in $S_J\\setminus\\mathrm{supp}(J)$, implements a factor of 16 between $a_j$ and the number of new centers.
- `Status:` counterexample (the conjecture "$\\ge\\ell/4$ associated centers per round" does not follow from Section 7.2).
- `InfoGain:` 1.
- `Barrier check:` r -- applicable (combinatorial counting is relativized), NP -- not applicable, alg -- not applicable.
- `Next step:` check in the original PDF that "centers" in Section 7.2 does not mean "chosen centers"; if not, embed the constant $64$ into the factor $M^{s/\\ell}$ and evaluate whether this gives something better than bound via $\\lceil s/\\ell\\rceil$.

### 16.204. Exploratory step (exact citation): "centers" in Section 7.2 are exposed centers (a subset of alive centers)

- `Lens:` Equivalence.
- `Statement (Q43.S38-quote-centers-exposed):`
  In HR'22, the "centers" in round stopping Section 7.2 are precisely exposed centers $S(\\lambda^j,\\sigma)$, and exposed centers are defined as a subset of alive centers.
- `Exact citation:`
  Definition of exposed centers: "1. a subset of the alive centers $S = S(\\tau,\\sigma)$ called the exposed centers" (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1841`).
  Stopping the round: "We continue with the next stage until at least $\\ell/4$ centers have been added in this round to the set of exposed centers $S(\\lambda^j,\\sigma)$ ..." (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2718–2719`).
- `Toy test:` substitution of definitions: the word "centers" in Section 7.2 directly refers to "set of exposed centers", without mentioning chosen centers.
- `Status:` confirmed (exact quote).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` compare the upper bound for the number of rounds via $\\lceil 64a/\\ell\\rceil$ with the factor $M^{\\lceil s/\\ell\\rceil}$ and show that the constant 64 does not worsen the result (Q43.S39-compare-round-bounds).

### 16.205. Research step (proof): 64 is absorbed by rescaling $\\ell$ ($\\ell\\ge t$  tcommon)

- `Lens:` Compression/canonization.
- `Statement (Q43.S39-absorb-64-rescale-ell):`
  In HR'22 Lemma 4.4, the $\\ell$ parameter is free (without $\\ell\\le t$ or $\\ell\\le s$ conditions), and if the input trees have depth $\\le t'$,
  then $\\ell$common partial decision tree for $\\ell\\ge t'$ is automatically $t'$common.
  Therefore, we can choose $\\ell:=64t'$ and get
  $$M^{\\lceil 64a/\\ell\\rceil}=M^{\\lceil a/t'\\rceil},$$
  and the factor $M^{s/\\ell}$ in Lemma 4.4 only decreases.
- `Proof:`
  1) Def. 2.10 and Lemma 4.4 do not impose restrictions on $\\ell$; $\\ell$ is included only as the depth of local trees and in the factor $M^{s/\\ell}$
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:574–582`, `…:1073–1084`).
  2) Let all $T_i$ have depth $\\le t'$, and let $T$ be a $\\ell$common partial tree with $\\ell\\ge t'$. For each branch $\\tau$ the constraint
     $T_i\\!\\upharpoonright\\!\\tau$ is a decision tree of depth $\\le t'$ (the depth does not increase with the constraint), and correctness/local consistency
     ensures the fact that $T$ is $\\ell$common. Then, choosing $T^{(i,\\tau)}:=T_i\\!\\upharpoonright\\!\\tau$, we obtain $t'$common partial tree.
  3) The substitution $\\ell:=64t'$ transforms $M^{\\lceil 64a/\\ell\\rceil}$ into $M^{\\lceil a/t'\\rceil}$, and $M^{s/\\ell}\\le M^{s/t'}$,
     therefore, the factor 64 is absorbed without degrading the probability estimate.
- `Toy test:` for $s=2$, $M=n^k$, $t'=(2s+1)\\log M$ and $\\ell=64t'$ conditions Lemma 4.4
  ($t'\\le s_\\eta\\le n'/32$) remain the same, and the factor over $M$ becomes $M^{\\lceil a/t'\\rceil}$.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable (parameter rescaling), NP - not applicable, alg - not applicable.
- `Next step:` check whether it is possible to bind $a$ to $s$ (for example $a\\le s$) or otherwise recalculate the corollary with the factor $M^{\\lceil a/t'\\rceil}$ - Q43.S40-bound-a-by-s.

### 16.206. Exploratory step (counterexample): non-chosen associated centers are not injected into queries, $a\\le s$ should not be

- `Lens:` Invariant.
- `Statement (Q43.S40-inject-a-to-queries):`
  Each disappearing center counted in $a$ corresponds to at least one request on branches $\\tau$,
  different centers give different requests, which means $a\\le s$.
- `Counterexample (structural):`
  In the HR'22 construction, the $\\tau$ branch requests **only** variables incident to the chosen centers:
  $S_J$ is defined as the set of chosen centers at a distance $\\le 1$ from $\\mathrm{supp}(J)\\cap C_\\sigma$,
  and $T$ is expanded by queries of all variables incident to $S_J$
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1943–1947`);
  Invariant 6.1(5) fixes that requests appear only from exposed chosen centers
  (`…:1858–1860`).
  But forceable branch $\\psi$ may contain variables with non-chosen associated center:
  Cor. 6.6 directly distinguishes between "associated center chosen/non-chosen" cases
  (`…:2024–2026`), and Def. 6.2(2) requires closing $J$ on such centers
  (`…:1886–1888`).
  Such non-chosen centers are included in $\\mathrm{supp}(J)\\setminus S^*_{j-1}$ and are taken into account in $a_j$,
  but they don't get into $S_J$, so they **don't create requests** for $\\tau$.
  Therefore, the injection "$a$ -> queries" does not work, and $a\\le s$ is not justified.
- `Toy test:` let $T_i$ have 1-branch from one edge $x_e$, whose associated center $u$ is non-chosen.
  Let us choose $\\sigma$ so that pairing $\\pi$ fixes the corresponding non-chosen path
  (Eq. (11), `…:1456–1467`), then $\\psi$ pairwise locally consistent with $\\sigma$.
  By Def. 6.2(2) $J$ is closed on $u$, so $a_j=1$, but $\\mathrm{supp}(J)\\cap C_\\sigma=\\varnothing$
  and $S_J=\\varnothing$, i.e. no queries are added to $\\tau$.
- `Status:` counterexample (injection breaks on non-chosen centers).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` divide $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$ and check
  Is it possible to bound $a_{\\mathrm{ch}}$ through $s$, and the contribution of $a_{\\mathrm{nch}}$ be reformulated in parameters,
  not requiring $a\\le s$ (or proceed to optimizing the sum over $a$ without this step).

### 16.207. Research step (proof): $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$, round factor depends only on $a_{\\mathrm{ch}}$

- `Lens:` Invariant.
- `Statement (Q43.S41-split-a-ch-nch):`
  Let $a_{j,\\mathrm{ch}}$ be the number of **chosen** associated centers among the variables on $\\psi_j$,
  lying in $\\mathrm{supp}(J_j)\\setminus S^*_{j-1}$, and $a_{\\mathrm{ch}}:=\\sum_j a_{j,\\mathrm{ch}}$.
  Then $s\\le 64a_{\\mathrm{ch}}$, which means the factor for rounds can be estimated as
  $$M^{\\lceil s/\\ell\\rceil}\\le M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}.$$
  The contribution $a_{\\mathrm{nch}}$ is encoded via $\\pi$ and does not generate new queries.
- `Proof:`
  1) Non-chosen information is determined by pairing $\\pi$ and does not require queries in $T$
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1854–1866`), while
     $I$ does not contain paths between chosen and non-chosen centers
     (`…:1869–1870`). Therefore, only exposed **chosen** centers create requests.
  2) Let $S_{\\mathrm{ch}}(\\tau,\\sigma):=S(\\tau,\\sigma)\\cap C_\\sigma$.
     From Section 6.4: "only variables incident to exposed chosen centers are queried and each exposed center causes at most 4 queries"
     (`…:2049–2051`), which means there is a stage $g$ with $|S^*_g\\cap C_\\sigma|\\ge s/4$.
  3) At stage $j$, the set of new chosen centers lies in $\\mathrm{supp}(J_j)\\cap C_\\sigma$ and $S_J$.
     By the argument of Lemma 6.5 (restricted to chosen centers), each chosen center in $\\mathrm{supp}(J_j)$
     has a chosen neighbor in $\\mathrm{supp}(J_j)$, so
     $$|\\mathrm{supp}(J_j)\\cap C_\\sigma\\cup S_J|\\le 4|\\mathrm{supp}(J_j)\\cap C_\\sigma|.$$
     In addition, from the minimality of $J_j$ and the prohibition of chosen-non-chosen paths, it follows that every chosen center
     in $\\mathrm{supp}(J_j)$ or is itself an associated center variable on $\\psi_j$,
     or adjacent to such a chosen associated center; Means
     $$|\\mathrm{supp}(J_j)\\cap C_\\sigma|\\le 4a_{j,\\mathrm{ch}}.$$
     Consequently, at stage $j$ no more than $16a_{j,\\mathrm{ch}}$ chosen-centers are added, and
     $|S^*_g\\cap C_\\sigma|\\le 16a_{\\mathrm{ch}}$.
  4) Combining with step 2, we obtain $s\\le 4|S^*_g\\cap C_\\sigma|\\le 64a_{\\mathrm{ch}}$ and the required bound on
     $M^{\\lceil s/\\ell\\rceil}$.
- `Toy test:` $s=1$, $\\psi$ contains a variable with non-chosen associated center $u$.
  By Def. 6.2(2) $J$ is closed on $u$, and Invariant 6.1(4) + remark about $\\pi$ gives,
  that the necessary information is already in $\\pi$ and does not require queries (`…:1854–1866`);
  for $\\mathrm{supp}(J)\\cap C_\\sigma=\\varnothing$ we have $S_J=\\varnothing$, therefore
  The depth of the branch does not increase and the round score does not increase.
- `Status:` proven (for the round factor; $a\\log t$ in Lemma 6.9 still depends on $a$).
- `InfoGain:` 1.
- `Barrier check:` r -- applicable (encoding/center count), NP -- not applicable, alg -- not applicable.
- `Next step:` optimize the sum over $a$ without the assumption $a\\le s$ (Q43.S42-optimise-a-sum).

### 16.208. Research step (proof): $\\log t$ in Lemma 6.9 is needed only for chosen associated centers

- `Lens:` Compression/canonization.
- `Statement (Q43.S42-encode-nch-no-logt):`
  In the proof of Lemma 6.9, log t-bits are used only for **chosen** associated centers,
  whereas non-chosen associated centers are reconstructed from pairing $\\pi$ with a constant number of bits
  on the component structure and $O(\\log \\Delta)$ on node identification.
  Therefore, in the encoding estimate, $t^{a}$ can be replaced by $t^{a_{\\mathrm{ch}}}$, and the contribution
  $a_{\\mathrm{nch}}$ is transferred to the $\\Delta$-part.
- `Proof:`
  In the reconstruction of $J_j$ from signatures: for each associated center $u$,
  which is **chosen**, (up to 3) incident centers are read, and if such a center is already defined,
  it is selected by "first bit in the signature is 1" with a cost of $\\log t$ (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2468-2475`).
  After this, the "structure of $J_j$ on the chosen centers" is fixed (`…:2474-2476`).
  For non-chosen centers then "complete some connected components from the pairing $\\pi$",
  the component structure is encoded with a constant number of bits, and each node is reconstructed
  with price no more than $\\log \\Delta$ (`…:2476-2480`).
  This means that log t is involved only in identifying chosen centers, while non-chosen
  only $\\log \\Delta$ are paid.
- `Toy test:` one round, one variable per $\\psi_j$ with non-chosen associated center.
  According to the text of the $J_j$ reconstruction, for non-chosen only pairing $\\pi$ and
  $\\log \\Delta$ per nodes, without mentioning $\\log t$ (`…:2476-2480`).
- `Status:` proven (exact quotation in the proof of Lemma 6.9).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (encoding), NP - not applicable, alg - not applicable.
- `Next step:` rewrite the sum over $a_{\\mathrm{ch}},a_{\\mathrm{nch}}$ into Eq. (18) and check the geometry (Q43.S42-sum-split-geometric).

### 16.209. Exploratory step (proof): geometry of the sum after partitioning $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$

- `Lens:` Equivalence.
- `Statement (Q43.S43-sum-split-geometric):`
  In Eq. (18) HR'22 (sum $\\sum_a A_2^s(4t\\log n'/\\Delta)^a$) after replacing $t^a\\rightsquigarrow t^{a_{\\mathrm{ch}}}$
  and partitioning $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$ we obtain a factorization into two geometric series.
  For $\\ell\\ge 64t'$ the round factor satisfies $M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}\\le M^{a_{\\mathrm{ch}}/t'}$,
  That's why
  $$
  \\sum_{a_{\\mathrm{ch}},a_{\\mathrm{nch}}\\ge 0}
  A_2^s\\Bigl(\\frac{4t'\\log n'}{\\Delta}\\Bigr)^{a_{\\mathrm{ch}}}
  \\Bigl(\\frac{4\\log n'}{\\Delta}\\Bigr)^{a_{\\mathrm{nch}}}
  M^{a_{\\mathrm{ch}}/t'}
  =
  A_2^s\\Bigl(\\sum_{a_{\\mathrm{ch}}\\ge 0} r_{\\mathrm{ch}}^{a_{\\mathrm{ch}}}\\Bigr)
  \\Bigl(\\sum_{a_{\\mathrm{nch}}\\ge 0} r_{\\mathrm{nch}}^{a_{\\mathrm{nch}}}\\Bigr),
  $$
  where $r_{\\mathrm{ch}}:=(4t'\\log n'/\\Delta)\\cdot M^{1/t'}$ and $r_{\\mathrm{nch}}:=4\\log n'/\\Delta$.
  In HR mode (choosing $n_\\eta$ gives $t'\\log n'/\\Delta\\le c<1$) both ratios are $<1$, which means the sum is limited by a constant.
- `Proof:`
  From Eq. (18) HR'22 we have the sum $\\sum_a A_2^s(4t\\log n'/\\Delta)^a$ (see PDF, Eq. (18)). Per Section 16.208
  $t^a$ can be replaced by $t^{a_{\\mathrm{ch}}}$, that is
  $$(4t\\log n'/\\Delta)^a=(4t\\log n'/\\Delta)^{a_{\\mathrm{ch}}}(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}.$$
  After transferring to $t'= (2s+1)\\log M$ and taking into account the round multiplier (from Section 16.207), we obtain the indicated double amount.
  For $\\ell\\ge 64t'$ we have $M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}\\le M^{a_{\\mathrm{ch}}/t'}$, therefore
  the series in $a_{\\mathrm{ch}}$ has the relation $r_{\\mathrm{ch}}$, and the series in $a_{\\mathrm{nch}}$ has the relation $r_{\\mathrm{nch}}$.
  In HR parameters $\\Delta=\\Theta(n/n')$ and recursion $n_\\eta$ provides $t'\\log n'/\\Delta<1$,
  This means that both series are geometric and converge to a constant.
- `Toy test:` $s=2$, $\\ell=5$, $t'=5$; let's take $n'=2$ (so $\\log n'=1$), $M=2$ (then $t'=(2s+1)\\log M=5$)
  and $\\Delta=32$.
  Then $r_{\\mathrm{ch}}=(4\\cdot5/32)\\cdot 2^{1/5}\\approx 0.72$ and $r_{\\mathrm{nch}}=4/32=0.125$.
  The sum starts as $1+r_{\\mathrm{ch}}+r_{\\mathrm{nch}}+\\cdots$ and is equal to
  $1/\\bigl((1-r_{\\mathrm{ch}})(1-r_{\\mathrm{nch}})\\bigr)=O(1)$.
- `Status:` proven (factorization and geometricity after partitioning $a$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (probability estimate/score), NP - not applicable, alg - not applicable.
- `Next step:` evaluate the connection of $a_{\\mathrm{nch}}$ with $a_{\\mathrm{ch}}$ or $s$ (for example, through pairing $\\pi$),
  to remove the dependence on $a_{\\mathrm{nch}}$ in the principal amount (Q43.S44-bound-anonch).

### 16.210. Research step (proof): Eq. (18) after $t^a\\to t^{a_{\\mathrm{ch}}}$ does not contain $a_{\\mathrm{nch}}$ outside the $\\Delta$ part

- `Lens:` Equivalence.
- `Statement (Q43.S45-audit-eq18-anonch-free):`
  After replacing $t^a\\rightsquigarrow t^{a_{\\mathrm{ch}}}$ and for $\\ell\\ge 64t'$ the entire dependence on
  $a_{\\mathrm{nch}}$ in the sum Eq. (18) HR'22 remains only in the multiplier
  $(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}$; neither $A_2^s$ nor round factor
  $M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}$ do not depend on $a_{\\mathrm{nch}}$.
  Consequently, summation over $a_{\\mathrm{nch}}$ is purely geometric and does not require
  add. estimates $a_{\\mathrm{nch}}$ through $a_{\\mathrm{ch}}$ or $s$.
- `Proof:`
  In HR Eq. (18) there is a sum of the form $\\sum_a A_2^s(4t\\log n'/\\Delta)^a$
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2125-2134`).
  By Section 16.208, $t^a$ can be replaced by $t^{a_{\\mathrm{ch}}}$ and expanded
  $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$, from where
  $(4t\\log n'/\\Delta)^a=(4t'\\log n'/\\Delta)^{a_{\\mathrm{ch}}}(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}$.
  The round multiplier in flat local EF(s) depends only on the chosen centers
  ($M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}$ from Section 16.207) since nonchosen centers
  do not create requests. Since $A_2^s$ depends only on $s$, the only source
  depending on $a_{\\mathrm{nch}}$ is $(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}$,
  which means the summation over $a_{\\mathrm{nch}}$ is geometric.
- `Toy test:` let's take $a_{\\mathrm{ch}}=0$. Then the contribution is equal
  $A_2^s(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}$, without $t'$ and without $M$,
  which confirms the absence of hidden dependencies.
- `Status:` proven (audit Eq. (18): $a_{\\mathrm{nch}}$ only in the $\\Delta$ part).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check that the HR parameters are guaranteed to be $4\\log n'/\\Delta<1$
  (after substituting $\\Delta=\\Theta(n/n')$) and fix this in the main bound (Q43.S46-check-rnch-params).

### 16.211. Research step (proof): $r_{\\mathrm{nch}}<1$ from HR estimates by $\\Delta$

- `Lens:` Equivalence.
- `Statement (Q43.S48-delta-constant-bridge):`
  In the HR parameters, under the condition $n\\ge 20 C n'\\log n'$ we have $\\Delta\\ge 2C\\log n'$,
  and also $\\Delta\\ge n/(6n')$. Then
  $$
  r_{\\mathrm{nch}}=\\frac{4\\log n'}{\\Delta}\\le \\frac{2}{C}<1 \\quad (C\\ge 3),
  $$
  so the sum over $a_{\\mathrm{nch}}$ in Section 16.210 is limited to a constant.
- `Proof:`
  In HR after (14) it is clearly stated: from the assumption $n\\ge 20 n' C\\log n'$ it follows
  $\\Delta\\ge 2C\\log n'$, and further "claimed bound follows from the fact $\\Delta\\ge n/6 n'$"
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1567-1568`).
  By Section 16.209-Section 16.210 $r_{\\mathrm{nch}}=4\\log n'/\\Delta$, therefore
  $r_{\\mathrm{nch}}\\le 4\\log n'/(2C\\log n')=2/C<1$ for $C\\ge 3$.
- `Toy test:` the minimal case $n=20 C n'\\log n'$ gives $\\Delta\\ge 2C\\log n'$ and
  $r_{\\mathrm{nch}}\\le 2/C$; for $C=4$ we get $r_{\\mathrm{nch}}\\le 1/2$.
- `Status:` proven (constant $r_{\\mathrm{nch}}$ from HR estimates on $\\Delta$).
- `InfoGain:` 1.
- `Barrier check:` r--applicable (parameter estimation), NP--not applicable, alg--not applicable.
- `Next step:` substitute $r_{\\mathrm{nch}}<1$ into the final bound Eq. (18)
  and capture the constant in the main summary of Q43 (Q43.S49-finalize-geo-constant).

### 16.212. Research step (proof): $r_{\\mathrm{ch}}<1$ from HR parameters

- `Lens:` Trade-off.
- `Statement (Q43.S50-bound-rch-constant):`
  In the HR mode with $t':=(2s+1)\\log M$ and $s\\ge 1$ we have
  $$r_{\\mathrm{ch}}=\\Bigl(\\frac{4t'\\log n'}{\\Delta}\\Bigr)\\cdot M^{1/t'}\\le \\kappa<1$$
  for all sufficiently large $n$. More precisely, from the conditions
  $n/n'\\ge A t'\\log^4 n$ (Lemma 4.2) and $\\Delta\\ge n/(6n')$ follows
  $$r_{\\mathrm{ch}}\\le \\frac{24e^{1/2}}{A\\,\\log^3 n},$$
  so for $\\log^3 n\\ge 48e^{1/2}/A$ we can take $\\kappa=1/2$.
- `Proof:`
  From $t'=(2s+1)\\log M$ we obtain
  $$M^{1/t'}=\\exp\\!\\left(\\frac{1}{2s+1}\\right)\\le e^{1/2}$$
  for $s\\ge 1$. By HR Lemma 4.2, $n/n'\\ge A t'\\log^4 n$ holds
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:950-952`),
  and after (14) we have $\\Delta\\ge n/(6n')$
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1567-1568`).
  Then
  $$r_{\\mathrm{ch}}\\le \\frac{4t'\\log n'}{\\Delta}\\,e^{1/2}
  \\le \\frac{24t'\\log n'}{n/n'}\\,e^{1/2}
  \\le \\frac{24e^{1/2}}{A}\\cdot\\frac{\\log n'}{\\log^4 n}.$$
  Using $\\log n'\\le\\log n$, we obtain the indicated estimate
  $r_{\\mathrm{ch}}\\le 24e^{1/2}/(A\\log^3 n)$ and, therefore, $r_{\\mathrm{ch}}<1$
  for $n\\ge n_0(A)$.
- `Toy test:` $s=2$, $M=2$ give $t'=5$ and $M^{1/t'}=2^{1/5}\\approx 1.15$.
  If $A=1$ and $\\log n=32$, then
  $$r_{\\mathrm{ch}}\\le \\frac{24e^{1/2}}{32^3}\\approx 1.2\\cdot 10^{-3}<1.$$
- `Status:` proven (explicit constant for $r_{\\mathrm{ch}}$ with HR parameters).
- `InfoGain:` 1.
- `Barrier check:` r--applicable (parameter estimation), NP--not applicable, alg--not applicable.
- `Next step:` substitute $r_{\\mathrm{ch}}<1$ and $r_{\\mathrm{nch}}<1$ into Eq. (18)
  and capture the constant in the main summary of Q43 (Q43.S49-finalize-geo-constant).

### 16.213. Exploratory step (proof): explicit constant from geometric sum

- `Lens:` Invariant.
- `Statement (Q43.S51-geo-constant-explicit):`
  From the factorization of Section 16.209 we have
  $$
  \\sum_{a_{\\mathrm{ch}},a_{\\mathrm{nch}}\\ge 0}
  A_2^s\\,r_{\\mathrm{ch}}^{a_{\\mathrm{ch}}}\\,r_{\\mathrm{nch}}^{a_{\\mathrm{nch}}}
  =\\frac{A_2^s}{(1-r_{\\mathrm{ch}})(1-r_{\\mathrm{nch}})}.
  $$
  Under the conditions HR (C\\ge 3 and $n\\ge n_0(A)$) we can take
  $r_{\\mathrm{ch}}\\le 1/2$ (Section 16.212) and $r_{\\mathrm{nch}}\\le 2/3$ (Section 16.211), so
  sum in Eq. (18) is limited to $6\\,A_2^s$.
- `Proof:`
  The geometric sum over $a_{\\mathrm{ch}}$ is equal to $1/(1-r_{\\mathrm{ch}})$,
  by $a_{\\mathrm{nch}}$ - $1/(1-r_{\\mathrm{nch}})$ (Section 16.209). Received in Section 16.212
  $r_{\\mathrm{ch}}\\le 24e^{1/2}/(A\\log^3 n)$, so for $\\log^3 n\\ge 48e^{1/2}/A$
  we can take $r_{\\mathrm{ch}}\\le 1/2$. In Section 16.211 we have $r_{\\mathrm{nch}}\\le 2/C$,
  and for $C\\ge 3$ we obtain $r_{\\mathrm{nch}}\\le 2/3$. Then
  $1/((1-r_{\\mathrm{ch}})(1-r_{\\mathrm{nch}}))\\le 1/((1-1/2)(1-2/3))=6$.
- `Toy test:` substituting $r_{\\mathrm{ch}}=1/2$, $r_{\\mathrm{nch}}=2/3$ we get the factor 6.
  For the numbers from Section 16.209 ($s=2$, $M=2$, $\\Delta=32$) we have
  $r_{\\mathrm{ch}}\\approx 0.72$, $r_{\\mathrm{nch}}=0.125$ and final multiplier
  $1/((1-0.72)(1-0.125))\\approx 4.1\\le 6$.
- `Status:` proven (explicit constant in the sum Eq. (18)).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (summation), NP - not applicable, alg - not applicable.
- `Next step:` print explicit $n_0(A)$ for the condition $r_{\\mathrm{ch}}\\le 1/2$
  and compare with the requirement $n\\ge 20Cn'\\log n'$ (Q43.S52-explicit-n0).

### 16.214. Exploratory step (proof): explicit $n_0(A)$ for $r_{\\mathrm{ch}}\\le 1/2$

- `Lens:` Trade-off.
- `Statement (Q43.S52-explicit-n0-closedform):`
  Let $A>0$ from the conditions of HR Lemma 4.2 and the estimate
  $$r_{\\mathrm{ch}}\\le \\frac{24e^{1/2}}{A\\log^3 n}$$
  (Section 16.212). Then
  $$n_0(A):=\\left\\lceil \\exp\\!\\left(\\left(\\frac{48e^{1/2}}{A}\\right)^{1/3}\\right)\\right\\rceil$$
  guarantees $r_{\\mathrm{ch}}\\le 1/2$ for all $n\\ge n_0(A)$.
- `Proof:`
  From $r_{\\mathrm{ch}}\\le 24e^{1/2}/(A\\log^3 n)$ it follows that $r_{\\mathrm{ch}}\\le 1/2$
  sufficient for $\\log^3 n\\ge 48e^{1/2}/A$, i.e.
  $$\\log n\\ge \\left(\\frac{48e^{1/2}}{A}\\right)^{1/3}.$$
  Exponentiating, we get $n\\ge \\exp\\!\\left((48e^{1/2}/A)^{1/3}\\right)$; for integers $n$
  this is equivalent to $n\\ge n_0(A)$.
- `Toy test:` for $A=1$ we have $n_0=\\lceil e^{(48e^{1/2})^{1/3}}\\rceil=74$ and
  $r_{\\mathrm{ch}}\\le 24e^{1/2}/\\log^3 74\\approx 0.496<1/2$.
  For $A=10$ we get $n_0=8$ and $r_{\\mathrm{ch}}\\le 0.440<1/2$.
- `Status:` proven (explicit closed formula $n_0(A)$).
- `InfoGain:` 1.
- `Barrier check:` r--applicable (parameter estimation), NP--not applicable, alg--not applicable.
- `Next step:` compare the condition $n\\ge 20Cn'\\log n'$ with $n\\ge n_0(A)$
  (Q43.S53-compare-20cnlogn).

### 16.215. Exploratory step (exact citation): constant $A$ in Lemma 6.9/4.2 is not solved numerically

- `Lens:` Trade-off.
- `Statement (Q43.S53-extract-a-bound):`
  In HR'22, the constant $A$ in Lemma 6.9/4.2 is introduced as "some constant" without a numerical value;
  additional constants $A_1,A_2,A_3,A_4$ appear in the proof, also without estimates.
  Therefore, the explicit lower bound $A_{\\min}$ cannot be extracted from the text without detailed bit counting
  in recovery algorithms (Section 6.5/Appendix B), and comparison of $n\\ge 20Cn'\\log n'$ with $n\\ge n_0(A)$
  requires separate calculation of constants.
- `Proof (exact citation):`
  IN `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt` Lemma 6.9 is stated
  like "There is a constant A > 0 ... a log t + b log \\Delta + s * A many bits suffice to encode "
  (lines 2096-2101). At the end of the proof an additional "some constant" is listed
  values: "A1 |S*_g| ... for some constant A1", "another A2 |S*_g| ... for some constant A2",
  "There is a constant A3 > 0...", "some other constant A4" (lines 2551-2562). Numerical
  No estimates are given for these constants.
- `Toy test:` from $t\\le s$ it follows $s+16t+s/4\\le (69/4)s$, so we can take
  $A_3,A_4\\le 69/4$, but $A_1,A_2$ remain implicit, and therefore $A_{\\min}$ is not fixed.
- `Status:` partially (the constant $A$ exists, but is implicit).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (evaluation of constants), NP - not applicable, alg - not applicable.
- `Next step:` go through Appendix B / Algorithms 2-7 and write down an explicit upper bound
  by $A_1,A_2$ (how many bits per center/edge), then get explicit $A$ and compare $n_0(A)$
  with $20Cn'\\log n'$ (Q43.S54-bound-a1a2-bits).

### 16.216. Exploratory step (toy computation): toy-bound for $A_1$ from Algorithms 2-4

- `Lens:` Compression/canonization.
- `Statement (Q43.S54-bound-a1-from-alg2-4):`
  In the toy case $|S^{*}_g|=1$, $s=2$, $\\ell=5$ (one stage) pseudocode Algorithms 2-4
  reads at most 18 constant bits from $X$ beyond the terms $a\\log t$, $b\\log\\Delta$
  and $9|S^{*}_g|$. Therefore, for this case we can take $A_1\\le 18$.
- `Toy test:` for $|S^{*}_g|=1$ we have $g=1$ (since $|S^{*}_g|\\ge s/4$). In Algorithm 2
  the inner loop reads exactly one bit `discover=1` for a single assoc. center
  and one bit `discover=0` to end the stage (2 bits;
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3119-3127`).
  Considering the worst option in terms of constant bits (the center chosen),
  Algorithm 3 calls `GetPossiblyDeadCenter` no more than 4 times per destination
  signatures (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3166-3173`),
  giving 4 bits `known` (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3304`).
  Next `RecoverExposed` gives <=4 more calls (4 bits `known`;
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3259-3264`)
  and `RecoverNonExposed` gives <=4 bits `recover` plus <=4 bits `known`
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3283-3286,3304`).
  Total $2+4+4+8=18$ constant bits. Alternatively (center not selected)
  read $\\log 20\\le 5$ bits `cc` and <=8 bits `known`
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3182-3193,3304`),
  which gives <=15, so 18 remains the top estimate.
- `Status:` partially (toy case; the general bound on $A_1$ has not yet been output).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (counting constants), NP - not applicable, alg - not applicable.
- `Next step:` generalize the counting of constant bits to an arbitrary $|S^{*}_g|$
  and write out explicit $A_1$ (separating the contributions of $\\log t$, $\\log\\Delta$ and 9bit signatures).

### 16.217. Research step (toy computation): $|S^{*}_g|=2$ (one chosen + one non-chosen)

- `Lens:` Invariant.
- `Statement (Q43.S55-count-a1-per-center):`
  In the toy scenario $|S^{*}_g|=2$ with one chosen and one non-chosen center at $s=2$, $\\ell=5$
  Algorithms 2-4 read no more than 32 constant bits beyond $a\\log t$, $b\\log\\Delta$
  and $9|S^{*}_g|$. Consequently, the linear bound $A_1|S^{*}_g|$ is already executed with $A_1=18$.
- `Toy test:` here $g=1$ (since $|S^{*}_g|\\ge s/4$). Let both centers be found associative.
  centers on the $\\psi$ branch (worst case for constant bits). Then Algorithm 2 reads
  two bits `discover=1` and one bit `discover=0` (total 3 bits;
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3119-3127`).
  In Algorithm 3, up to 4 calls are possible for the chosen center `GetPossiblyDeadCenter`, everyone gives
  one bit `known` (4 bits; `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3166-3173,3304`).
  For non-chosen center: in the first cycle <=4 bits `known` (same lines), then read
  $\\log 20\\le 5$ bits `cc` and <=4 more bits `known` to restore components (total 13 bits;
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3182-3193,3304`).
  Next `RecoverExposed` for a single chosen center gives <=4 bits `known`, A
  `RecoverNonExposed` gives <=4 bits `recover` and <=4 bits `known`
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3259-3264,3283-3286,3304`).
  Total $3+4+13+12=32$ constant bits; since $32\\le 18\\cdot 2$, linearity in
  $|S^{*}_g|$ is stored at this toy level.
- `Status:` proven (toy case; linear scaling confirmed).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (counting constants), NP - not applicable, alg - not applicable.
- `Next step:` go to general $|S^{*}_g|$: output percenter bound, carefully take into account
  the only one `discover=0` per stage and get an explicit $A_1$.

### 16.218. Research step (toy scan): local arXiv-slice does not provide a direct link to the "common partial decision tree" / "multi-switching"

- `Lens:` Experiment.
- `Statement (Q43.S56a-arxiv-scan):`
  In a local arXiv slice `resources/arxiv/pvnp_slice.tsv` there are no direct matches for phrases
  "common partial decision tree" or "multiswitching"; matches for "Tseitin" indicate HR'22,
  and for "switching lemma" - only for a general overview/project. A ready-made link to the "a-sum trick" in the metadata
  not visible.
- `Toy test:`
  1) `rg -ni "common partial decision tree|multi-switching" resources/arxiv/pvnp_slice.tsv` -> no matches.
  2) `rg -ni "tseitin" resources/arxiv/pvnp_slice.tsv | head -20` -> there is HR'22 (`…:13`).
  3) `rg -ni "switching lemma" resources/arxiv/pvnp_slice.tsv | head -20` -> there is a general overview (`…:149`).
- `Status:` no direct links found (local slice).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` continue Q43.S56-generalize-a1-per-center.

### 16.219. Research step (toy computation): $|S^{*}_g|=3$ (two chosen + one non-chosen)

- `Lens:` Compression/canonization.
- `Statement (Q43.S56-generalize-a1-per-center):`
  In the toy scenario $|S^{*}_g|=3$ (two chosen + one non-chosen) with $s=2$, $\\ell=5$
  Algorithms 2-4 read no more than 49 constant bits beyond $a\\log t$, $b\\log\\Delta$
  and $9|S^{*}_g|$. Therefore, $49\\le 18\\cdot |S^{*}_g|$ and linearity in
  $|S^{*}_g|$ is stored at this toy level.
- `Toy test:` here $g=1$ (since $|S^{*}_g|\\ge s/4$). Let's assume that all three
  centers found as assoc. centers on the $\\psi$ branch (worse for constant bits).
  Algorithm 2 reads three bits `discover=1` and one bit `discover=0` (4 bits;
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3119-3127`).
  In Algorithm 3, the first loop gives up to 4 calls `GetPossiblyDeadCenter` to the center, i.e.
  12 bit `known` (`…:3166-3173,3304`). For a non-chosen center, additionally read
  $\\log 20\\le 5$ bits `cc` and <=4 more bits `known` when restoring components
  (`…:3182-3193,3304`), a total of 21 bits in Algorithm 3. Next `RecoverExposed` gives
  <=4 bits `known` to chosencenter (8 bits; `…:3259-3264,3304`), A `RecoverNonExposed`
  gives <=4 bits `recover` and <=4 bits `known` to chosencenter (16 bits; `…:3283-3286,3304`).
  A total of $4+21+24=49$ constant bits, which is <= $18\\cdot 3=54$.
- `Status:` partially (toy case; general $A_1$ has not yet been printed).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (counting constants), NP - not applicable, alg - not applicable.
- `Next step:` try to derive a general percenter invariant
  "each associatedcenter is detected at most once" and thereby obtain
  global $A_1$ (Q43.S57-invariant-one-discovery).

### 16.220. Research step (proof): onediscovery for associated centers

- `Lens:` Invariant.
- `Statement (Q43.S57-one-discovery-proof):`
  If the associated center $u$ of a variable on a forceable branch $\\psi_j$ does not lie in $S^{*}_{j-1}$,
  then $u$ becomes disappearing center exactly at this stage; therefore, there are 2 bits in Algorithm
  `discover=1` is read no more than once per center, and the number of such bits is $\\le |\\mathrm{supp}(K^{*})|\\le |S^{*}_g|$.
- `Proof:`
  1) By Def. 6.2(2), if the associated center $u$ of a variable on $\\psi_j$ is not in $S^{*}_{j-1}$, then $J_j$ is closed in $u$
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1886-1888`), and such $u$ are disappearing centers
     (`…:2255-2257`). Therefore $u\\in\\mathrm{supp}(J_j)=\\mathrm{supp}(K_j)$.
  2) By Lemma 6.7 supports $J_j$ and $J_{j'}$ are discrete for $j\\ne j'$ (`…:2028-2041`), means any disappearing center
     belongs to a single stage.
  3) Update $S(\\tau',\\sigma)=S(\\tau,\\sigma)\\cup S_J\\cup\\mathrm{supp}(J)$ (`…:1949-1952`)
     and Invariant 6.1(1) ("S is only growing", `…:1838-1842`) give: after stage $j$ the same $u$ is already in $S^{*}_{j}$,
     therefore, in subsequent stages it cannot enter $\\mathrm{supp}(J_{j'})\\setminus S^{*}_{j'-1}$ again.
  4) Algorithm has 2 bits `discover=1` read only for disappearing center, which is the associated center
     variable on $\\psi$ (`…:3119-3124`), which means each such $u$ gives <=1 reading. Because
     $\\bigcup_{j\\le g}\\mathrm{supp}(J_j)\\subseteq S^{*}_g$, the number of these bits is $\\le |S^{*}_g|$.
- `Toy test:` two-stage scenario: let the same center $u$ try to be an associated center on $\\psi_j$
  and $\\psi_{j+1}$ for $u\\notin S^{*}_{j-1}$. Then $u\\in\\mathrm{supp}(J_j)$ by Def. 6.2(2), but Lemma 6.7
  prohibits $u\\in\\mathrm{supp}(J_{j+1})$--a contradiction. If $u\\in S^{*}_j$, then it does not participate in $a_{j+1}$
  and does not require `discover=1`.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` use onediscovery for full percenter counting of constant bits in Algorithms 2-4
  and output explicit $A_1$ (Q43.S58-bound-a1-constant).

### 16.221. Research step (proof): Algorithm 3 gives <=13 constant bits per center

- `Lens:` Compression/canonization.
- `Statement (Q43.S59-alg3-per-center-constant):`
  In Algorithm 3 (RecoverForcingInformation) the total number of constant bits (known/recover/cc)
  of $X$ read at stages $j\\le g$ does not exceed $13\\,|S^{*}_g|$. Equivalent to everyone
  the center of $S^{*}_g$ can be assigned <=13 such bits.
- `Proof:`
  1) In the first loop of Algorithm 3, each associated center $v\\in E_{\\psi}$ causes `GetPossiblyDeadCenter`
     no more than 4 times (per direction), and each call reads exactly one bit `known`
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3161-3173,3304`).
     For a non-chosen center, the second loop adds $\\log 20\\le 5$ bits `cc` and <=4 more bits `known`
     when restoring components (`…:3177-3193,3304`), total <=13 constant bits.
  2) For chosen-centers from $\\mathrm{supp}(J)$ Lemma 6.5 gives the presence of a neighboring chosen-center in
     $\\mathrm{supp}(J)$ (`…:2013-2017`), so in `RecoverExposed` at least one among 4 directions
     already contains the chosen center, and `GetPossiblyDeadCenter` called <=3 times (<=3 bits `known`;
     `…:3259-3264,3304`).
  3) Each chosen-center $u\\in S$ has a neighboring chosen-center in $S$: if $u\\in\\mathrm{supp}(J)$ --
     by Lemma 6.5, otherwise $u$ is added `RecoverExposed` from the sub-square adjacent to such
     center. Then in `RecoverNonExposed` the condition "no chosen center" can be satisfied
     in no more than 3 directions, giving <=3 bits `recover` and <=3 bits `known`
     (`…:3279-3286,3304`).
  4) Therefore, each chosen associated center gives <=$4+3+6=13$ constant bits,
     and any other chosen centers found through `RecoverExposed`, give <=$1+6\\le 7$.
     By Lemma 6.7 supports $J_j$ are discrete (`…:2028-2036`), and $S$ is monotone
     (Invariant 6.1(1) and update $S(\\tau',\\sigma)$; `…:1842-1844,1949-1952`),
     therefore, each center from $S^{*}_g$ is processed at most once. Result:
     <=$13\\,|S^{*}_g|$ constant bits.
- `Toy test:` for the toy case $|S^{*}_g|=3$ the estimates from Section 16.219 can be strengthened:
  replacing "4 directions" with "<=3" in `RecoverExposed/RecoverNonExposed`, we get
  $21+6+12=39\\le 13|S^{*}_g|$.
- `Status:` proven (linear percenter bound for Algorithm 3).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (bit counting), NP - not applicable, alg - not applicable.
- `Next step:` close Algorithm 2 contribution (`discover=0` per stage) and collect explicit $A_1$
  along with Algorithm 4 (Q43.S58-alg2-discover-budget).

### 16.222. Research step (proof): `discover=0` limited by number of centers

- `Lens:` Invariant.
- `Statement (Q43.S60-bound-g-by-centers):`
  In Algorithm 2 the number of bits `discover=0` is equal to the number of stages $g$, and $g\\le |S^{*}_g|$.
  Therefore, the contribution `discover=0` in $A_1$ does not exceed $|S^{*}_g|$.
- `Proof:`
  1) In Algorithm 2, step 3 reads bit $b$; if $b=1$, the procedure remains in the same stage
     and returns to step 3, and if $b=0$, then step 5 is executed and stage $j$ ends
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2381-2388`).
     This means that there is exactly one bit per stage `discover=0`, and their number is $g$.
  2) $g$ is the first stage, where $|S^{*}_g|\\ge s/4$ (`…:2043-2051`), and the text explicitly states,
     that "at each stage at least one center is added to $S$", whence $g\\le s/4$
     (`…:2052-2054`). Therefore, $g\\le s/4\\le |S^{*}_g|$.
  3) Combining (1)-(2), we obtain the required contribution estimate `discover=0`.
- `Toy test:` for $|S^{*}_g|=1$ it is inevitable that $g=1$ (since $|S^{*}_g|\\ge s/4$),
  and Algorithm 2 actually reads exactly one bit `discover=0` at a single stage.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` evaluate constant bits in Algorithm 4 and collect explicit $A_1$
  (Q43.S61-alg4-constant).

### 16.223. Research step (proof): Algorithm 4 does not read X  contribution 0

- `Lens:` Invariant.
- `Statement (Q43.S61-alg4-constant):`
  Algorithm 4 (RecoverK) does not read bits from $X$; the set $K$ is calculated
  deterministically from $J$ and $I^{*}_{-}$. Therefore, the contribution of Algorithm 4 to the number
  of constant bits is equal to $0$ (and, in particular, $\\le C\\,|S^{*}_g|$ for $C=1$).
- `Proof:`
  1) Algorithm 4 pseudocode only accepts $I^{*}_{-}$ and $J$ and does not contain calls
     To `next bit from X`; operations are traversing $u\\in\\mathrm{supp}(J)$ and adding
     non-edges $(u,\\delta,\\bot)$ in $K$
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:3230-3238`).
  2) The direction of $\\delta$ is determined from the already restored $J$ and $I^{*}_{-}$
     as a direction without information in $J\\cup I^{*}_{-}$; this calculation does not require
     reading additional bits.
  3) Therefore, the total contribution of Algorithm 4 to constant bits is $0$.
- `Toy test:` for $s=2$, $\\ell=5$ and $|S^{*}_g|\\in\\{1,2\\}$ Algorithm 4 does not read $X$,
  therefore, the toy counts from Section 16.216-Section 16.217 do not change.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - applicable (bit counting), NP - not applicable, alg - not applicable.
- `Next step:` collect explicit $A_1$ as the sum of contributions of Algorithms 2-4 and fix
  final constant (Q43.S62-assemble-a1).

### 16.224. Research step (proof): explicit $A_1$ from the sum of contributions of Algorithms 2-4

- `Lens:` Invariant.
- `Statement (Q43.S62-assemble-a1-sum):`
  Total number of constant bits read in Algorithms 2-4, plus signatures read
  (no more than $9|S^{*}_g|$) is limited to $24|S^{*}_g|$. Equivalently, you can take
  explicit constant $A_1^{\\mathrm{tot}}=24$ for the entire "constant-part" term in Lemma 6.9.
  If you keep the signatures separately, then $A_1\\le 15$.
- `Proof:`
  1) According to Section 16.220 bits `discover=1` read no more than once per center, i.e.
     no more than $|S^{*}_g|$ bits.
  2) According to Section 16.222 bits `discover=0` are equal to the number of stages and do not exceed $|S^{*}_g|$.
  3) By Section 16.221 Algorithm 3 gives <= $13|S^{*}_g|$ constant bits (known/recover/cc).
  4) According to Section 16.223, Algorithm 4 does not read $X$, the contribution is 0.
  5) Reading signatures gives <= $9 more|S^{*}_g|$ bits
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2549`).
  Adding, we get $9+1+1+13=24$ bits per center; with separate accounting of signatures
  that leaves $A_1\\le 15$.
- `Toy test:` with $|S^{*}_g|=4$ (2 chosen + 2 non-chosen) the total worst-case is equal to
  $4+4+13\\cdot 4+9\\cdot 4=96=24\\cdot 4$, which is consistent with bound $A_1^{\\mathrm{tot}}|S^{*}_g|$.
- `Status:` proven (the explicit constant $A_1$ is obtained by summing the contributions).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (bit counting), NP - not applicable, alg - not applicable.
- `Next step:` evaluate explicit $A_2$ for structure $J_j$ and $I^{*}_{-}$ to get
  fully numerical constants Lemma 6.9 (Q43.S63-bound-a2-graph-structure).

### 16.225. Exploratory step (proof): explicit $A_2$ for structure $J_j$ and $I^{*}_{-}$

- `Lens:` Compression/canonization.
- `Statement (Q43.S63-bound-a2-graph-structure):`
  For each center there are exactly 4 directions (left/right/up/down), so the structure
  information set (specifically $J_j$ or $I_j$) is encoded with <=2 bits per direction
  (no information/non-edge/edge), i.e. <=8 bits per center. Therefore, for the total
  structures $J_j$ and $I^{*}_{-}$, we can take an explicit constant $A_2\\le 16$.
- `Proof:`
  1) By Def. 5.6 information piece -- either edge $\\{v,w\\}$ between neighboring centers, or
     non-edge $(v,\\delta,\\bot)$ with $\\delta\\in\\{\\text{left},\\text{right},\\text{up},\\text{down}\\}$,
     those. exactly 4 directions to the center
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1586-1590`).
  2) In the HR text, the $J_j$ structure is restored using "constant number of bits per potential edge"
     (`…:2259-2261`), and $I_j$ requires the same constant type
     (`…:2536-2539`); the final contribution is summed up to $A_2|S^{*}_g|$ (`…:2555`).
  3) With known support centers (log $\\Delta$ bits are taken into account separately) for each direction
     There remains a triple choice: no information / non-edge / edge. This is encoded in 2 bits,
     means <=8 bits per center for $J_j$ and <=8 bits per center for $I_j$.
  4) In total, we can take an explicit $A_2:=16$ for the structure $J_j$ and $I^{*}_{-}$.
- `Toy test:` $s=2$, one chosencenter. The center has 4 directions; 2 bits per direction give
  8 bits for structure $J_j$ and 8 bits for structure $I_j$, total 16 = $A_2\\cdot|S^{*}_g|$
  for $|S^{*}_g|=1$.
- `Status:` proven (explicit constant $A_2$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable (bit counting), NP - not applicable, alg - not applicable.
- `Next step:` check if $A_2$ can be absorbed into signature/structure $J_j$
  (Q43.S64-absorb-a2-into-signature).

### 16.226. Exploratory step (counterexample): signatures do not capture the structure of $I_j$

- `Lens:` Compression/canonization.
- `Statement (Q43.S64-absorb-a2-by-signature):`
  Definition 6.11 signatures capture only the structure $J_j$ and do not define the structure $I_j$;
  already in the toy example there are two different $I_j$ with the same signatures and support, so
  $A_2=0$ should not be.
- `Counterexample / Toy test:`
  Let at stage $j$ the set of exposed centers $S_j$ be a 2x2 block of chosen centers, and $J_j$
  (and his signatures) are fixed. By Invariant 6.1(2) $I_j$ must be locally consistent and
  is closed on $S_j$ (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1841-1848`),
  and the closedness/oddness of the degrees is specified by Definition 5.8 and 5.11
  (`…:1618-1623,1659-1665`). Then two different closed $I_j$ are possible on the same support:
  $I_j^{H}$ with horizontal matching (two horizontal edges) and $I_j^{V}$ with vertical matching
  matching. In both cases, each center has exactly one incident edge (odd degree),
  and the remaining directions are occupied by non-edge information, so local consistency
  is saved. Signatures depend only on $J_j$ (`…:2327-2333`), so for $I_j^{H}$ and $I_j^{V}$
  they are the same, but the structures are different. Therefore, signatures/support do not define $I_j$,
  and a separate $A_2$ term is needed.
- `Status:` counterexample (absorption of $A_2$ in the signature is impossible in its current form).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check if $O(1)$ bits can be added to the center of the signature so that
  encode structure $I_j$ while maintaining constant size (Q43.S66-tradeoff-augment-signature).

### 16.227. Exploratory step (proof): loops provide 1 bit of ambiguity $I_j$

- `Lens:` Trade-off.
- `Statement (Q43.S68-tree-uniqueness-cycle-bit):`
  Let us fix support and the graph of possible edges $G$ on these centers (the edge between the centers
  in adjacent sub-squares, Definition 5.6). Then every closed $I$ on a given support
  is equivalent to choosing a subset of edges $E(I)\\subseteq E(G)$ in which each vertex
  odd degree; the set of such $I$ has size $2^{\\beta(G)}$, where $\\beta(G)$ is the cyclomatic
  number. In particular, if $G$ is a forest, then $I$ is unique.
- `Proof:`
  1) According to Definition 5.6, any information in the direction is either edgepiece $\\{v,w\\}$,
     or non-edge $(v,\\delta,\\bot)$ (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1586-1590`).
     For fixed support: if there is no center in the direction, then nonedge is required,
     if there is a center, the choice "edge vs non-edge" determines the presence of an edge. So $I$
     is completely specified by the set of edges $E(I)$ in the graph of possible edges $G$.
  2) According to Definition 5.8 and 5.11, local consistency and closedness to support give
     "an odd number of edges at each vertex" (`…:1618-1623,1659-1665`), i.e. $E(I)$ --
     odd-degree subgraph $G$.
  3) Let $I$ and $I'$ be two closed sets on one support. Then in $E(I)\\oplus E(I')$
     each vertex has an even degree (odd  odd = even), which means $E(I)\\oplus E(I')$
     decomposes into a disjoint union of cycles. Hence the set of solutions is affine
     space of dimension $\\beta(G)$, and $|\\{I\\}|=2^{\\beta(G)}$.
  4) If $G$ is a forest (there are no cycles), then $E(I)\\oplus E(I')=\\varnothing$ and $I=I'$; every
     an independent loop adds exactly 1 bit (loop switching preserves odd powers).
- `Toy test:` a path of 4 centers (tree) admits exactly one $I$; 2x2 center block has
  $\\beta=1$ and gives two $I$ (horizontal/vertical matching), as in Section 16.226.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to encode the choice of cycle basis $G$ in $O(1)$ bits per center
  (for example, through a fixed spanning forest + bits on chords) and check if it fits
  it's in the Definition 6.11 signature (Q43.S69-encode-cycle-basis-bits).

### 16.228. Research step (proof): canonical skeleton + chord bits

- `Lens:` Compression/canonization.
- `Statement (Q43.S69-encode-cycle-basis-bits):`
  For a fixed support and a possible edge graph $G$ (Definition 5.6) there is
  canonical spanning forest $F(G)$ and canonical odddegree subgraph $E_0\\subseteq F(G)$
  such that any closed $I$ with this support satisfies
  $E(I)=E_0\\oplus\\bigoplus_{e\\in\\mathrm{Chords}(G)} b_e C_e$, where $C_e$ is the fundamental
  the cycle of the chord $e$, and the bits $b_e\\in\\{0,1\\}$ can be stored at the ends of the chords using
  $\\le$4 extra bits per center.
- `Proof:`
  1) Let us fix the canonical order of centers (for example, lexicographic) and construct
     $F(G)$ as BFSforest. If a closed $I$ exists, then in each component of $G$
     the number of vertices is even: the sum of odd powers is $2|E(I)|$ (even). Then on the tree
     $F$ there is exactly one subgraph with odd degree at each vertex (solution
     parity systems on the tree; built by removing leaves). Let's denote it $E_0$.
  2) For any closed $I$, the subgraph $D:=E(I)\\oplus E_0$ has even degrees in each
     vertex, that is, lies in cycle space $G$. According to the standard fact, cycle space
     is generated by fundamental cycles of chords $e\\in E(G)\\setminus E(F)$, and the coefficients
     $b_e$ are unique in this expansion.
  3) Each chord $e=\\{u,v\\}$ corresponds to the direction y of $u$ and $v$. Store $b_e$ at the end
     with a smaller lexicographic identifier; the center has a maximum of 4 incident edges,
     This means it stores <=4 bits of chords.
  4) Reconstruction: we start from $E_0$ and for each chord from $b_e=1$ we switch the edges to
     cycle $C_e$ (chord + unique path in $F$ between ends). We get $E(I)$.
- `Toy test:` 2x2 block of centers. Canonical $F$ is a path of 3 edges; $E_0$ -- two non-adjacent
  ribs A single chord gives a cycle of length 4: $b=0$ gives one matching, $b=1$ gives the second.
  23 ladder: $|V|=6$, $|E|=7$, $|E(F)|=5$, which means two chords. $E_0$ is fixed on the tree,
  and two bits of chords give 4 closed $I$, which is the same as $2^{\\beta(G)}$.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check that adding 4 bits per center is consistent with Def. 6.11/Def. 6.13
  and does not break the conflict criterion (i.e. does not require center identifiers).

### 16.229. Exploratory step (proof): integration of chord bits into signatures

- `Lens:` Compression/canonization.
- `Statement (Q43.S70-integrate-chord-bits-signature):`
  If the Definition 6.11 signature is extended with an additional <=4 bits per center,
  encoding the choice of chords from Section 16.228, then Definition 6.13 and Algorithms 2-4 remain
  are correct without changing the reading logic: the conflict check uses only 9-bit
  signature prefix, and new bits participate only in restoring the $I_j$ structure.
- `Proof:`
  1) Definition 6.11 signature is 9 bits per center (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2332`),
     read together with a fixed center (`…:2336-2338`). Therefore, you can attach to the signature
     local bits $b_e$ for chords assigned to this center (<=4 per center per Section 16.228), without encoding
     no "personality" of the center - the center is known by the order of reading.
  2) Definition 6.13 defines a conflict through partial assignment on incident directions,
     specified by the first and second quadruples of signature bits (`…:2345-2367`). Additional chord beats
     these eight bits do not change, which means predicate "conflict" coincides with the original one after projection
     to a 9-bit prefix.
  3) In the recovery procedure (Algorithms 2-4), signatures are read as constant blocks of bits and
     are added to $E$ (`…:2378-2385`); the logic of steps 1-5 uses only conflict and recovery
     $J_j$. Therefore, you can read extended signatures and save chord bits until they are restored
     $I_j$. By Section 16.228, the canonical skeleton $F(G)$ together with the set $b_e$ uniquely reconstructs
     $E(I_j)$; this only adds <=$4|S^{*}_g|$ bits and does not change the reading logic.
  4) Therefore, adding <=4 bits per center is compatible with Definition 6.13 and algorithms.
- `Toy test:` 22 block of chosencenters. For fixed support two $I_j$ are possible
  (horizontal/vertical matching, Section 16.226). The canonical spanning tree gives one chord and bit $b$.
  We fix $b=0$ and get $I_j^{H}$. Any branch of $\\psi$ containing a variable on the vertical
  edge, together with $I_j^{H}$ violates pairwise local consistency in Definition 6.13(2), so
  conflict-check cuts off an incompatible branch for a fixed $b$.
- `Status:` proven.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether the chord bit assignment rule violates the requirement
  “signature does not include identity” (Q43.S72-identity-leak-check-chord-bits).

### 16.230. Exploratory step (counterexample): chord bits depend on global numbering

- `Lens:` Invariant.
- `Statement (Q43.S72-identity-leak-check-chord-bits):`
  In the Section 16.228-16.229 extension, the additional chord bits per center depend only on the local
  structures (support + incident directions) and are invariant under grid automorphisms,
  therefore the extended signature does not encode the identity of the center (Remark 6.12).
- `Counterexample / Toy test:`
  Let's take support = 22 block of centers. The graph of possible edges $G$ is a square. Canonical
  the skeleton $F(G)$ from Section 16.228 constructs a BFS with lexicographic order of centers: three edges
  are included in $F(G)$, and the only chord is the fourth edge of the square. This chord connects
  two diagonally symmetrical centers. By rule Section 16.228, bit $b_e$ is stored at the end
  chords with a smaller lexicographic identifier. If we apply square symmetry
  (rotate/flip) and rename the directions, then 9bit signatures Definition 6.11
  are converted equivariantly, but the rule is "smaller lexicographic ID stores bit"
  not preserved: the chord carries the bit to another angle. So the extended signature depends
  from the global numbering of centers and is not invariant under symmetry.
- `Status:` counterexample (identity-leak for the chord bit assignment rule Section 16.228).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` redefine the assignment of chord bits locally canonically (without
  global numbering) or explicitly fix the allowed grid orientation
  (Q43.S74-local-reencode-chord-bits).

### 16.231. Exploratory step (toy): local rule for assigning chord bits by direction

- `Lens:` Compression/canonization.
- `Statement (Q43.S74-dir-rule-chord-bits):`
  With a fixed grid orientation, the bit of each chord $e=\\{u,v\\}$ can be assigned locally:
  store $b_e$ at the end for which the direction to the neighbor is minimal in a fixed
  order, for example South < West < North < East (that is, the "south" or "west" end).
  This uses only directional labels, does not require global center numbering, saves
  <=4 bits per center and does not change the Definition 6.13 conflict check (it depends only on the 9-bit
  signature prefix).
- `Toy test:`
  1) 2x2 block of centers. A single chord is one edge of a square. The bit is stored in "south/west"
     end of the chord; when transferring a block (translation), the edge direction and end selection are preserved,
     therefore, the distribution of bits by center does not depend on absolute coordinates. Conflict check
     uses only the first 9 bits of the signature (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2345-2367`),
     so the extra chord bits are ignored.
  2) 23 ladder. Two chords: each horizontal/vertical, the bit is stored in the western
     or the south end. Any ladder transfer preserves the directions and distribution of bits;
     at each center <=4 incident directions  <=4 bits.
- `Status:` partially (toy confirmation; general correctness and admissibility of fixed
  orientations have not yet been proven).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check on general support whether fixed orientation is causing problems
  (South/Westrule) of hidden identityleak for symmetries, and whether it is necessary to explicitly fix
  grid orientation in the model.

### 16.232. Exploratory step (proof): fixed orientation does not give identityleak

- `Lens:` Model stress test.
- `Statement (Q43.S75-orientation-leak-check):`
  If the grid is considered as oriented (directions N/E/S/W are fixed and already
  are used in Definition 6.11), then the rule is "the chord bit is stored at the south/west end"
  depends only on the directions of the incident edges, is invariant under support transfers and not
  encodes the identity of the center (Remark 6.12).
- `Proof:`
  1) Definition 6.11 specifies a signature of 9 bits, where two fours correspond to directions
     (information pieces + presence of edges), and Remark 6.12 emphasizes that the signature does not include
     identity center (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2337`).
     Therefore, fixed directions are already a valid part of the local
     information.
  2) South/West rule selects the end of the chord in the direction of the edge (south/west), that is
     uses only local direction labels and does not refer to global numbering or
     coordinates. Therefore, any orientation-preserving automorphism (translation) preserves
     distribution of chord bits.
  3) In symmetrical support (22, 23), an attempt to "change the end" through rotation/reflection changes
     directions of incident edges, which means it does not save the 9-bit signature; such symmetries are not
     valid for fixed orientation. Consequently, locally isomorphic (preserving
     directions) there are no environments with different chord beats.
- `Toy test:` 2x2 and 2x3: transfers preserve directions and selection of the "south/west" end;
  reflection/rotation changes the direction bits in the signature and is not a valid isomorphy.
- `Status:` proven (with a fixed grid orientation already used in the signature).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if the orientation is not considered part of the structure (rotations/reflections are allowed),
  build canonical anchor/orientation from one signature (Q43.S76-anchor-canonicalization).

### 16.233. Exploratory step (exact citation): in HR'22 the grid orientation is fixed by coordinates and directions

- `Lens:` Equivalence.
- `Statement (Q43.S78-orientation-explicit-quote):`
  In HR'22, the grid is defined as an oriented structure with fixed coordinates (i, j)  [n] and
  explicitly used left/right/up/down directions and line numbering; means rotations/reflections
  are not valid symmetries of the default model.
- `Exact link (HR'22, text cache):`
  1) definition of grid through coordinates: `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:395–399`
     (“Throughout the paper we work over graphs Gn = (V, E) with n2 nodes which we call the grid.
      However, in order to avoid problems at the boundary, we in fact work over the 2-dimensional
      torus: each node (i, j) ∈ V is indexed by two integers i, j ∈ [n] and an edge {u, v} is in E if and
      only if it connects two adjacent nodes, that is, if one of the coordinates of u and v are identical
      and the other differs by 1 modulo n.”)
  2) left/right/up/down directions are given in terms of relative position: `…:1382–1384`
     (“Given a fixed center v we say that a path P connecting v to some other center u goes to the δ,
      where δ is one of the directions left, right, up or down, if v lies in the sub-square to the δ of u.”)
  3) line numbering is used: `…:1403–1405`
     (“… fixing the alive centers with the lowest numbered row in each sub-square to be the chosen
      centers Cσ of σ.”)
- `Toy test:` not required (the quotation fixes the structure of the model).
- `Status:` exact citation.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if an orientation-free model is considered (with rotations/reflections),
  anchor canonization is needed (Q43.S76); otherwise return to main track Q43.

### 16.234. Exploratory step (counterexample): single-signature data does not capture orientation

- `Lens:` Model stress test.
- `Statement (Q43.S79-symmetry-counterexample):`
  In an orientation-free model (allowing rotations/reflections) of one center signature
  (Definition 6.11, even with added local chord bits) is not enough to be canonical
  fix orientation: there is symmetrical support, where a 180 rotation leaves
  single-signature data remains unchanged, but changes orientation.
- `Counterexample / Toy test:`
  1) Let's take support as a "cross" of 5 centers: central v and its four neighbors along N/E/S/W.
     The graph of possible edges here is a tree, so there are no chord bits. Let v be chosen (chosen),
     and in J_j v has information pieces in all four directions and all four are present
     incident ribs. Then the signature v has the form (chosen=1; info=1111; edges=1111)
     (Definition 6.11 in `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2332`).
  2) A 180 rotation or reflection preserves this "cross", fixes v and rearranges the directions.
     In the orientation-free model, this is an admissible automorphism. Since all four direction bits
     v are the same, the signature of v is invariant under this permutation.
  3) Therefore, two opposite orientations (N/E/S/W and S/W/N/E) are compatible with the same
     signed v; any procedure using only one signature cannot choose between them
     without additional symmetry breaking bit.
- `Status:` counterexample (canonization of orientation from one signature is impossible in the orientation-free model).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether it is enough to add one global chirality bit or another
  minimal symmetry-breaking marker to the signature to fix the orientation without identity-leak
  (Q43.S80-chirality-bit).

### 16.235. Exploratory step (counterexample): global chirality bit does not break symmetry

- `Lens:` Compression/canonization.
- `Statement (Q43.S80-chirality-bit):`
  Adding one global bit $\\chi$, common to all centers and independent of their identity
  (Remark 6.12), 9bit signatures are sufficient to canonically fix orientation in
  orientation-free model.
- `Counterexample / Toy test:`
  1) Suppose that $\\chi$ is calculated from unlabeledsupport and a set of signatures, that is, it is invariant
     regarding grid automorphisms (otherwise it uses identity centers). Let's take the "cross" from 5
     centers as in Section 16.234, with chosen center $v$ and signature $(1;1111;1111)$. Rotate $180^\\circ$
     preserves support and all signatures, so $\\chi$ has the same meaning. Therefore, extended
     signatures (signature+$\\chi$) are the same for two opposite orientations.
  2) Similarly for a 22 block of centers with a symmetric set of local data: $180^\\circ$rotation
     rearranges the angles, but preserves the multiset of signatures, and the global invariant $\\chi$ remains
     the same. Orientation based on extended signatures is not recorded.
- `Status:` counterexample (one global invariant bit does not fix orientation without identity).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if you resolve the external "orientation" value $\\chi$ as an advice bit, check if
  that it does not violate Remark 6.12 and only adds $O(1)$ bits to Algorithms 2-4; otherwise fix
  that the orientation-free model requires a non-invariant anchor.

### 16.236. Research step (proof): advice bit orientation $\\chi$ compatible with Remark 6.12

- `Lens:` Model stress test.
- `Statement (Q43.S81-chirality-advice-check):`
  If we allow one global non-invariant advice bit $\\chi$ that fixes the orientation of the grid,
  then Algorithms 2-4 use it with the addition of $O(1)$ bits, the signatures remain identityfree
  (Remark 6.12), and the combination signature+$\\chi$ sets the orientation for all support.
- `Proof:`
  1) Remark 6.12 fixes that the center signature does not contain its identity and is read together with
     given center $v$; the order of the signatures is part of the external information, but is not encoded in the signature
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2338`). Global
     the $\\chi$ bit is not centered and does not change the 9bit signature, so it does not violate the requirement
     “no identity in signature”.
  2) Algorithms 2-4 read signatures as constant blocks of bits and use direction only
     incident edges/sub-squares (Algorithm 2: reading 9 bits of signature; Algorithm 3-4: working on
     directions and sub-squares) (`…:3089-3133`, `…:3161-3173`, `…:3234-3238`). Hence,
     $\\chi$ can be considered a global parameter that determines the interpretation of directions
     (for example, "clockwise/anticlockwise" orientation); it is enough to read it once
     at the beginning of Algorithm 2. This only adds $O(1)$ bits and requires no per-center data.
  3) For a fixed $\\chi$, the directions in the signature are interpreted relative to the chosen orientation,
     so the orientation is determined globally (all processing in Algorithms 2-4 is consistent across
     this choice). Therefore, signature+$\\chi$ specifies the orientation without additional identity code.
- `Toy test:` "cross" and 2x2 block from Section 16.234-16.235. For each support, the algorithm reads only
  9-bit signatures and direction-dependent checks. If you choose $\\chi=0$ as "standard"
  orientation, all calls to Algorithms 2-4 interpret directions the same; turn 180
  corresponds to the change of $\\chi$ and does not require access to the coordinates of the centers. Therefore, $\\chi$
  splits symmetries into two orientations without identity-leak.
- `Status:` proven (advice bit is valid and adds $O(1)$ bits).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` estimate the minimum number of global bits for orientation canonicalization (e.g.
  distinguish all 8 symmetries $D_4$) and compare with the variant $|\\chi|=1$ (Q43.S83-min-orientation-bits).

### 16.237. Research step (proof): $D_4$symmetry requires >=3 global bits for orientation

- `Lens:` Invariant.
- `Statement (Q43.S83-d4-lower-bound):`
  In the orientation-free model, there is support and a set of 9-bit signatures, whose
  the data is invariant under all 8 $D_4$ symmetries; therefore, any identityfree
  Orientation canonicalization requires >=3 global bits.
- `Proof:`
  1) Construction. Let's take support as a "cross" of 5 centers on the grid: central $v$ and
     four neighbors on N/E/S/W. Let all centers be chosen. Let's set the signature $v$ as
     $(1;1111;1111)$ (there are information pieces and edges in all directions), and the signatures
     leaves - as $(1;1000;1000)$, $(1;0100;0100)$, $(1;0010;0010)$, $(1;0001;0001)$
     depending on the direction to $v$. This distribution is realized by $J_j$ containing
     exactly four $v$-leaf edges and information along these directions.
  2) Any symmetry $g \\in D_4$ (rotation/reflection) preserves support and rearranges
     directions N/E/S/W. The signature $v$ is invariant (all directions =1), and the four leaf
     the signatures are simply rearranged. Therefore, the multiset of signatures is invariant
     under all 8 symmetries.
  3) Let $A$ be an identity-free orientation canonizer that reads support, signatures, and $k$
     global advice bit. For this symmetric support, all 8 orientations are consistent with
     input, and can only differ in advice bits. Therefore $2^k \\ge 8$, that is
     $k \\ge 3$.
- `Toy test:` cross: $D_4$ rearranges leaves and directions, but multiset of signatures
  does not change; the orientation remains indistinguishable without external bits.
- `Status:` proven (information-theoretical lower bound: >=3 global bits).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` build an explicit 3-bit orientation canonicalization scheme compatible
  with Algorithms 2-4 (Q43.S84-3bit-upper).

### 16.238. Research step (proof): 3bit orientation canonization (upper bound)

- `Lens:` Compression/canonization.
- `Statement (Q43.S84-3bit-upper):`
  In the orientation-free model, you can set the global advice code $\\omega\\in\\{0,1\\}^3$,
  encoding element $D_4$, and interpret the direction bits in the signatures relative to $\\omega$.
  This code is read once before Algorithms 2-4, does not depend on identity centers,
  is not added to 9-bit signatures and does not change the Definition 6.13 conflict check.
- `Proof:`
  1) Let us fix the encoding $D_4$: let $b_2b_1b_0\\in\\{0,1\\}^3$; if $b_2=0$, take a turn
     $r^{k}$ (where $k=2b_1+b_0$) by $0/90/180/270^\\circ$, and if $b_2=1$, take the reflection
     $s\\circ r^{k}$ (where $s$ is the reflection relative to the vertical). This is the bijection $\\{0,1\\}^3\\leftrightarrow D_4$.
  2) Definition 6.11 sets the center signature as 9 bits: chosen, four direction bits for information
     pieces and four direction bits for edges (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2332`),
     and Remark 6.12 prohibits identity in the signature (`…:2333-2336`). For fixed $g\\in D_4$ we treat
     these bits as data in the directions $g(N),g(E),g(S),g(W)$. This is a global renaming of directions,
     the same for all centers, so identity information does not appear.
  3) Algorithm 2 reads the signature as exactly 9 bits (`…:3122-3124`), and conflict check Definition 6.13 is based on
     only for these 9 bits and $I$. Algorithms 2-4 further use only directional indices when working
     with sub-squares (`…:3164-3169`), so the interpretation via $g$ is implemented once and does not change
     logic of algorithms.
- `Toy test:`
  "Cross", 2x2 block, 2x3 ladder. For each support, any $D_4$ symmetry only rearranges
  directions; the $\\omega$ code selects $g$ and thereby fixes the correspondence of the direction bits N/E/S/W.
  Signatures remain 9-bit, the conflict check depends only on the prefix, so
  the logic of Algorithms 2-4 is preserved in all three examples.
- `Status:` proven (3bit global advice sets orientation without identityleak).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check if these 3 bits can be calculated from support+signatures without
  external advice (anchor canonization) or get local impossibility (Q43.S85/Q43.S86).

### 16.239. Research step (toy computation): admissibility of a D4symmetric "cross"

- `Lens:` Model stress test.
- `Statement (Q43.S86-admissible-d4-support):`
  There is D4symmetrical support+signatures from Section 16.237 (cross with central signature
  $(1;1111;1111)$), which is valid as possible forcing information $J_j$ (Definition 6.2)
  and can occur in inputs of Algorithms 2-4.
- `Toy test:`
  1) In Section 16.237, the central center $v$ is assigned a signature with info=1111 and edges=1111, that is
     $J_j$ has information in all four directions and 4 incident edges
     (Definition 6.11, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2332`).
  2) By local consistency, if there is information in all 4 directions, the number
     incident edges must be odd (`…:1618-1623`). Here 4 (even), which means
     such $J_j$ is not locally consistent and violates Def. 6.2(1) (`…:1882-1886`).
- `Status:` a counterexample to the admissibility of this D4symmetric "cross" as support $J_j$.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` or find D4symmetric support that satisfies the local
  consistency (odddegree), or prove that such support is impossible in the model.

### 16.240. Research step (proof): D4 + fixed-center are incompatible with odd-degree

- `Lens:` Invariant.
- `Statement (Q43.S87-fixed-center-parity):`
  Let $I$ be a closed information set (Def. 5.11 in HR'22), $U:=\\mathrm{supp}(I)$. If $U$
  D4 is symmetric with respect to a fixed center $c\\in U$, then such $I$ does not exist:
  closed $\\Rightarrow$ the edge graph on $U$ has odd degrees (1 or 3), so $|U|$ is even,
  but D4 symmetry with a fixed center gives $|U|$ odd.
- `Proof:`
  1) By Def. 5.11 and local consistency, for each $u\\in U$ the information is given in all
     4 directions, and the number of incident edges of $u$ is odd; means the graph of edges on $U$ --
     odddegree (degrees 1 or 3). See HR'22, remark after Def. 5.11
     (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1664-1679`).
  2) By the handshake lemma, the number of vertices with odd degree is even; hence $|U|$ is even.
  3) If $U$ is invariant under $D_4$ and contains a fixed center $c$, then all others
     orbits are size 4 or 8 (points on axes/diagonals or general case) so
     $|U|=1+4a+8b$ and $|U|$ is odd. Contradiction.
- `Toy test:` "cross" (5 centers) and 3x3 block (9 centers): both have D4 symmetry
  with a fixed-center, but $|\\mathrm{supp}|$ is odd, which means odd-degree is impossible.
- `Status:` proven (all D4symmetric closedsupports with a fixedcenter are excluded).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check D4symmetrical closedsupports without fixedcenter
  (orbits 4/8), or write mod-2 inconsistency (Q43.S88).

### 16.241. Exploratory step (counterexample): D4 quota is too strong

- `Lens:` Equivalence.
- `Statement (Q43.S88-quotient-parity):`
  An attempt to reduce the existence of D4symmetric closedsupport (without a fixedcenter)
  to the system of parities on orbital variables (D4-quotient) is incorrect: such a system
  describes only D4-invariant sets of edges and may be inconsistent even when
  closedsupport exists.
- `Toy test:`
  1) On a 4x4 grid, take support $U$ = central 2x2 block. It is D4symmetrical and does not contain
     fixed center. The induced graph is a cycle $C_4$, and a closed $I$ exists: for example,
     horizontal (or vertical) matching gives odd powers of 1 for all vertices
     (odddegree  closed, Def. 5.11 + remark after it,
     `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1659-1679`).
  2) If we require D4 symmetry for the edges (orbital variables on the D4 quota),
     then $C_4$ has one edge orbit (all 4 edges), and any vertex is incident to it twice.
     Therefore, any D4symmetric edge selection gives even degrees (0 or 2),
     and the equation $\\deg(v)\\equiv 1\\pmod 2$ is inconsistent.
- `Status:` counterexample (quotient parity captures only D4-invariant $I$).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` look for a restriction on supports without a fixed center, which prohibits
  any odddegree subgraphs (without the requirement of D4symmetry of edges), or go to
  orbit8only design (Q43.S88b).

### 16.242. Research step (toy computation): orbit8only support at 66 with odddegree

- `Lens:` Compression/canonization.
- `Statement (Q43.S89-orbit8-construction):`
  On a 66 grid there is a D4symmetric closedsupport without a fixedcenter, consisting only
  from orbit8centers, on which there is an odddegree subgraph; it means there is closed information
  set (Def. 5.11 in HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1659-1670`).
- `Toy test:`
  1) We use coordinates $(i,j)\\in[6]^2$ and symmetries $D_4$ of the square relative to the center
     $(3.5,3.5)$. Let's take the orbit of the point $(2,3)$:
     $$U=\\{(2,3),(2,4),(3,2),(3,5),(4,2),(4,5),(5,3),(5,4)\\}.$$
     All vertices of $U$ are outside the diagonals $i=j$ and $i+j=7$, so the orbit has size 8
     (orbit8only) and $U$ D4symmetric.
  2) In the grid neighborhood graph, select the edges
     $$E=\\{(2,3)(2,4),(3,2)(4,2),(3,5)(4,5),(5,3)(5,4)\\}.$$
     Then each $u\\in U$ has degree $1$ (odd).
  3) Define information set $I$ as $E$ plus non-edges in all other directions
     incident $u\\in U$. By Def. 5.8 local consistency condition is satisfied
     (odd‑degree; `…:1618-1623`), and according to Def. 5.11 $I$ -- closed.
- `Status:` proven (explicit construction on 6x6).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether such orbit8 supports are compatible with the requirements
  possible forcing information $J_j$ (Def. 6.2), or find additional local obstruction.

### 16.243. Research step (counterexample): orbit8 support is not excluded locally

- `Lens:` Invariant.
- `Statement (Q43.S91-orbit8-jj-local-obstruction):`
  Orbit8 support on 66 cannot be support possible forcinginformation $J_j$:
  local consistency (Def. 6.2(1)) and the chosen-non-chosen edges prohibition already give
  local parity conflict.
- `Toy test:`
  1) Take orbit8 support $U$ and edges $E$ from Section 16.242 (4 disjoint edges).
     Let $J$ contain these 4 edges and non-edges in all other directions for each
     $u\\in U$. Then $J$ is locally consistent: information in all 4 directions and exactly
     1 incident edge (odd) for each $u$ (Def. 5.8).
  2) Let $I=\\varnothing$ (or $\\mathrm{supp}(I)\\cap U=\\varnothing$), then Def. 6.2(1) is satisfied.
     If all centers in $U$ are of the same type (all chosen or all non-chosen), then the ban
     chosen-non-chosen edges are observed automatically.
  3) In the case of non-chosen centers, take pairing $\\pi$ with 4 edge components $E$;
     then $J\\!\upharpoonright_{\\text{nonchosen}}$ is the union of the components of $\\pi$,
     those. Def. 6.2(4) is satisfied.
  4) For the branch $\\psi$, consisting of variables with associative centers $U$, $J$ is closed at
     each $u$ and therefore all variables are forced (Def. 5.9), and deleting
     any information piece is broken by forcing, i.e. $J$ is minimal.
- `Status:` counterexample (no local obstruction: Def. 6.2(1) + chosen-non-chosen prohibition
  do not exclude orbit8 support).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` check the compatibility of such $J_j$ with real restrictions on $S/I/\\pi$
  in the canonical tree (global conditions), or formalize the mod-2 system for
  orbit8 with chosen/nonchosen split.

### 16.244. Research step (toy computation): orbit-8 and 2-stage canonical fragment

- `Lens:` Model stress test.
- `Statement (Q43.S94-orbit8-canonical-fragment):`
  An attempt to exclude orbit-8 as a stage of the canonical tree via Def. 6.2(3) or Def. 6.13(2)
  does not work on a 2-stage toy fragment: there is a choice $(\\rho,I,S,\\pi,\\psi)$, where $J_j$
  of Section 16.243 satisfies Def. 6.2(1-4), and there is no conflict with Definition 6.13(2).
- `Toy test:`
  1) Take orbit8 support $U$ and $J$ from Section 16.243. Let's put $I=\\varnothing$ and $S=\\varnothing$.
     Then Def. 6.2(1) is true (pairwise local consistency), and Def. 6.2(2) is trivial,
     because $J$ is closed on every $u\\in U$ (information in all 4 directions).
  2) Take the branch $\\psi$ with variables, associative. $U$ centers. By Def. 5.9 each like this
     variable forced, hence Def. 6.2(3) is satisfied, and the minimality of $J$ follows
     from the fact that removing any piece on $u$ removes forcing from the center $u$.
  3) If all centers $U$ are nonchosen, then Def. 6.2(4) holds for pairing $\\pi$,
     whose components coincide with 4 edges of $E$; and in Def. 6.13(2) set $E_\\psi$
     is empty, and assignment from $I$ is trivially pairwiselocally consistent.
  4) If all centers are $U$ chosen, then the signatures (Definition 6.11) encode the same scheme
     edges/non-edges, same as $J$; induced assignment on a smaller lattice is locally consistent
     (odddegree 1 on each $u$), so Def. 6.13(2) also gives no conflict.
- `Status:` partially (toy fragment is compatible with Def. 6.2(3) and Def. 6.13(2); obstruction not found).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` write a global mod-2 system for orbit-8 with a given partition
  chosen/non-chosen and pairing $\\pi$ (Q43.S95).

### 16.245. Research step (toy computation): orbit-8 mod-2 global check (all-non-chosen)

- `Lens:` Invariant.
- `Statement (Q43.S95-orbit8-mod2-global):`
  For allnonchosen support $U$ and pairing $\\pi=E$ global conflict Definition 6.13(2)
  reduces to the linear system $A x=b$ over $\\mathbb F_2$ along the edges $\\pi$; for 6x6 orbit8
  from Section 16.242 the system is solvable (the unique solution $x_e=1$ for all $e\\in E$).
- `Toy test:`
  1) With allnonchosen and $\\pi=E$ assignment on the selected paths, only
     information pieces at non-chosen centers. Local consistency (Def. 5.8) gives
     equation $\\sum_{e\\ni v} x_e = 1$ for each $v\\in U$ (odddegree).
  2) We number the edges $e_1=(2,3)(2,4)$, $e_2=(3,2)(4,2)$, $e_3=(3,5)(4,5)$, $e_4=(5,3)(5,4)$.
     Then
     $$A=\\begin{pmatrix}
     1&0&0&0\\\\
     1&0&0&0\\\\
     0&1&0&0\\\\
     0&1&0&0\\\\
     0&0&1&0\\\\
     0&0&1&0\\\\
     0&0&0&1\\\\
     0&0&0&1
     \\end{pmatrix},\\quad b=\\mathbf 1,$$
     and the system is equivalent to $x_1=x_2=x_3=x_4=1$ (rank$=4$), i.e. joint
- `Status:` proven (mod2 check does not give a conflict in the allnonchosen case).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check mixed chosen/non-chosen: write a system for 2 chosen + 6 non-chosen
  and check for Definition 6.13(2) conflict.

### 16.246. Research step (toy computation): orbit8 mixed chosen/nonchosen, mod2 check

- `Lens:` Invariant.
- `Statement (Q43.S96-orbit8-mixed-chosen-conflict):`
  On orbit8 support $U$ from Section 16.242 when choosing chosen centers $(2,3)$ and $(5,4)$ and the rest
  non-chosen, if $J$ uses edges $E$ from Section 16.242, then mod-2 check Definition 6.13(2)
  remains compatible (as in the allnonchosen case).
- `Toy test:`
  1) Take $U$ and $E$ from Section 16.242. Let's denote
     $e_1=(2,3)(2,4)$, $e_2=(3,2)(4,2)$, $e_3=(3,5)(4,5)$, $e_4=(5,3)(5,4)$ and
     variables $x_i\\in\\{0,1\}$ for these edges.
  2) Let the chosen centers be $c_1=(2,3)$ and $c_2=(5,4)$, the remaining 6 centers are non-chosen, and $J$
     contains edges $E$ and non-edges in all other directions, i.e. the information is complete
     on each $u\\in U$.
  3) Local consistency gives the equations $\\sum_{e\\ni u} x_e = 1$ for all $u\\in U$,
     which is equivalent to $x_1=x_2=x_3=x_4=1$ (the system is the same as Section 16.245) and therefore
     joint
  4) Note: edges $e_1,e_4$ connect chosen-non-chosen and violate Def. 6.2(4); Here
     Only conflict check Def is checked. 6.13(2).
- `Status:` toy computation (Definition 6.13(2) conflict not detected in this configuration).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` repeat mod-2 check when choosing-non-chosen edges are prohibited (Def. 6.2(4)),
  for example, select adjacent chosen centers or fix $x_{e_1}=x_{e_4}=0$ and check
  compatibility.

### 16.247. Research step (toy computation): orbit8 prohibition chosen-nonchosen -> $x_{e_1}=x_{e_4}=0$

- `Lens:` Compression/canonization.
- `Statement (Q43.S97-orbit8-force-e1e4-zero):`
  In a Section 16.246 configuration, the chosen-non-chosen edges prohibition (Def. 6.2(4)) is equivalent to committing
  $x_{e_1}=x_{e_4}=0$ in mod2 system Section 16.245; then the system $A x=\\mathbf 1$ is inconsistent,
  so the Definition 6.13(2) conflict arises at the toy level.
- `Toy test:`
  1) Let us leave support $U$ and chosen centers $c_1=(2,3)$, $c_2=(5,4)$ as in Section 16.246.
     The edges $e_1=(2,3)(2,4)$ and $e_4=(5,3)(5,4)$ connect chosen-non-chosen, so in $J$
     must be non-edges: $x_{e_1}=x_{e_4}=0$.
  2) In the system $A x=\\mathbf 1$ from Section 16.245 the lines for $(2,3),(2,4)$ give $x_{e_1}=1$,
     and the lines for $(5,3),(5,4)$ give $x_{e_4}=1$. Contradiction with $x_{e_1}=x_{e_4}=0$,
     therefore the system is inconsistent.
- `Status:` proven (mod-2 conflict when mixed-edges are prohibited).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check an alternative configuration without mixed-edges, for example adjacent chosen
  centers and a new $J$ without edges chosen-non-chosen (Q43.S98).

### 16.248. Research step (toy computation): orbit8 adjacent chosen without mixededges

- `Lens:` Invariant.
- `Statement (Q43.S98-adjacent-chosen-mod2-conflict):`
  In orbit8 support $U$ with adjacent chosen centers $(2,3)$ and $(2,4)$, chosen-nonchosen edges prohibition
  (Def. 6.2(4)) and $J$ with edges $E$ from Section 16.242 mod2 system $A x=\\mathbf 1$
  inconsistent (conflict Def. 6.13(2)).
- `Toy test:`
  1) Take $U$ and edges $E$ from Section 16.242, denote
     $e_1=(2,3)(2,4)$, $e_2=(3,2)(4,2)$, $e_3=(3,5)(4,5)$, $e_4=(5,3)(5,4)$ and $x_i\\in\\{0,1\}$.
  2) Choose chosen centers $c_1=(2,3)$ and $c_2=(2,4)$ (adjacent), the remaining 6 centers are non-chosen;
     let $J$ contain edges $E$ and non-edges in all other directions, so that the information
     is complete on every $u\\in U$. Then among $E$ there are no chosen-non-chosen edges: $e_1$ connects
     chosen-chosen, and $e_2,e_3,e_4$ - non-chosen-non-chosen.
  3) Local consistency gives the same system $A x=\\mathbf 1$ from Section 16.245,
     those. $x_1=x_2=x_3=x_4=1$. The mixed-edges ban does not fix any $x_i$,
     therefore the system is cooperative and conflict Def. 6.13(2) does not arise.
- `Status:` counterexample (adjacent chosen does not entail a mod-2 conflict in this configuration).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.

### 16.249. Research step (exact citation): adjacent chosen are allowed by Def. 5.6/6.2/6.11

- `Lens:` Equivalence.
- `Statement (Q43.S99-adjacent-chosen-allowed):`
  In HR'22, the definitions do not prohibit a minimal $J$ with exactly two adjacent chosen centers and without
  chosen-non-chosen ribs; Section 16.248 configuration is allowed under Def. 5.6/6.2/6.11, and Lemma 6.5
  requires the presence of adjacency between chosen centers in $\\mathrm{supp}(J)$.
- `Exact citation:`
  “Edges between chosen centers are new grid edges and we say that two chosen centers are neighbors
  if they lie in adjacent sub-squares” (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1571-1574`).
  Definition 5.6: information is either the edge between centers in adjacent subsquares,
  or non-edge $(v,\\delta,\\bot)$ (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1586-1594`).
  Definition 6.2: possible $J$ is a minimal set with conditions (1)-(4) and an explicit remark
  “a possible forcing information $J$ never contains an edge between a chosen center and a non-chosen center”
  (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1882-1893`).
  Lemma 6.5 uses $J$ minimality and local consistency to show:
  “every chosen center in $\\mathrm{supp}(J)$ is adjacent to at least one other chosen center in $\\mathrm{supp}(J)$”
  (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2016-2023`).
  Definition 6.11 specifies the 9bit signature of the center (chosenbit, information directions, edge directions),
  without restrictions on adjacency (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2327-2332`).
- `Toy test:`
  1) In the configuration Section 16.248 we take chosen centers $c_1=(2,3)$ and $c_2=(2,4)$ (adjacent),
     $J$ contains edge $e_1=c_1c_2$ and edges $e_2,e_3,e_4$ between non-chosen centers, and
     other directions are closed non-edges.
  2) Def. 5.6 allows such information pieces (edge between adjacent centers and non-edge records).
  3) There is no violation of "no chosen-nonchosen edges": $e_1$ connects chosen-chosen, $e_2,e_3,e_4$ --
     non-chosen-non-chosen, which is consistent with Def. 6.2(4) and an explicit remark after Def. 6.2.
  4) Local consistency is satisfied (exactly one piece per direction and odd degree),
     so if $I$ is locally consistent (e.g. $I=\\varnothing$), Def holds. 6.2(1).
  5) Signatures Def. 6.11 are correctly defined: the selected centers have bit chosen = 1, all directions are marked
     and exactly one direction with an edge, so adjacency does not create a ban.
- `Status:` confirmed (adjacent chosen are allowed at the definition level; there is no prohibition).
- `InfoGain:` 1.
- `Barrier check:` r - not applicable (quote/wording), NP - not applicable, alg - not applicable.
- `Next step:` check whether minimal $J$ with exactly two adjacent chosen centers can
  actually arise as possible forcing information (Def. 6.2(3)), or >=3 chosen are required (Q43.S101).

### 16.250. Research step (toy computation): 2 adjacent chosen give possible forcing information

- `Lens:` Model stress test.
- `Statement (Q43.S101-two-chosen-example):`
  On a 4x4 grid there is a configuration with exactly two adjacent chosen centers, for which
  one can choose $(\\rho,I,S,\\pi,\\psi)$ such that $J$ is possible forcing information
  (Def. 6.2) and minimal (Def. 5.9), while $J$ does not contain chosen-non-chosen edges.
- `Toy test:`
  1) Take adjacent chosen centers $c_1=(2,3)$ and $c_2=(2,4)$, the remaining centers are outside support.
     Let's put $I=\\varnothing$, $S=\\varnothing$, $\\pi=\\varnothing$, and $\\psi$ is a branch,
     containing at least one variable associated with each of $c_1,c_2$.
  2) Define $J$ as edge $\\{c_1,c_2\\}$ and non-edges $(c_1,\\delta,\\bot)$ for the other three
     directions from $c_1$ and similarly for $c_2$. Then $J$ is closed at $c_1,c_2$
     (Def. 5.11; `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1659-1664`)
     and locally consistent (on one incident edge - odd degree, Def. 5.8).
     Therefore, Def. 6.2(1) is satisfied.
  3) Since $S=\\varnothing$, Def. 6.2(2) requires closure in $c_1,c_2$, which is satisfied.
  4) By Def. 5.9 the presence of information in all 4 directions for $c_1,c_2$ forces
     all variables associated with these centers; means all variables are $\\psi$ forced
     and Def. 6.2(3) is satisfied. If you remove any piece in $J$, one of the centers ceases to be
     closed, and the variable on $\\psi$ at this center is not forced - therefore $J$ is minimal.
  5) $J$ does not contain non-chosen centers, which means Def. 6.2(4) is trivially fulfilled
     (the empty subset of $\\pi$ components), and chosen-non-chosen edges are absent.
- `Status:` proven (toy example: $J$ with 2 adjacent chosen is possible).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether global constraints impose an invariant on the $S/I/\\pi$
  mindegree>=2 or linear ambiguity, excluding support from 2 chosen (Q43.S102).

### 16.251. Exploratory step (counterexample): global restrictions on $S/I/\\pi$ do not give mindegree>=2

- `Lens:` Invariant.
- `Statement (Q43.S102-degree2-invariant):`
  If possible forcing information $J$ has exactly two adjacent chosen centers, then global
  restrictions on $S/I/\\pi$ force mindegree>=2 in the graph $\\mathrm{supp}(J)$, so the toy example
  from Section 16.250 is not possible.
- `Toy test:`
  1) Take the configuration Section 16.250: two chosen centers $c_1,c_2$, $J$ contains the edge $\\{c_1,c_2\\}$
     and three non-edges from each center; $I=\\varnothing$, $S=\\varnothing$, $\\pi=\\varnothing$.
  2) By Def. 6.2(2) with $S=\\varnothing$ each associated center on the branch $\\psi$ must be
     closed; this is exactly executed, and Def. 6.2(4) is trivial (there are no non-chosen centers).
  3) By Def. 5.9 variables on $\\psi$ forced **only** if there is information in all 4 directions;
     removing any piece in $J$ removes the closedness and destroys the forcedness, so that $J$ is minimal.
  4) The graph $\\mathrm{supp}(J)$ has degree 1 for both chosen centers (the only edge between them),
     and it is compatible with Def. 6.2(1-4). Consequently, global restrictions on $S/I/\\pi$ do not give
     invariant mindegree>=2.
- `Status:` counterexample (the mindegree>=2 invariant does not follow).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check linear ambiguity $I/\\pi$ for fixed support for two
  adjacent chosen (Q43.S103-linear-ambiguity-2chosen).

### 16.252. Exploratory step (toy computation): adjacent chosen does not give linear ambiguity

- `Lens:` Invariant.
- `Statement (Q43.S103-ambiguity-construct):`
  In configuration Section 16.250 with two adjacent chosen and without chosen-non-chosen edges
  linear system for closed information set on fixed support has
  the only solution; therefore, (I,) on this support are single-valued, and
  there is no linear ambiguity.
- `Toy test:`
  1) We fix support $U=\\{c_1=(2,3),c_2=(2,4)\\}$ from Section 16.250; there are no non-chosen centers,
     so pairing $\\pi=\\varnothing$.
  2) The graph of possible edges $G$ on $U$ has a single edge $e=\\{c_1,c_2\\}$.
     Let $x_e\\in\\{0,1\\}$ be the presence of an edgepiece between $c_1,c_2$.
  3) Closedness and local consistency (Def. 5.8/5.11:
     `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1618-1623,1659-1665`)
     require an odd degree on each $v\\in U$, that is
     $$A=\\begin{pmatrix}1\\\\1\\end{pmatrix},\\quad A x=\\mathbf 1,$$
     whence $x_e=1$.
  4) Therefore, for a fixed support there is exactly one closed information set,
     and there is no freedom in $I/\\pi$ (with the same signatures).
- `Status:` counterexample (there is no linear ambiguity: the solution is unique).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check the criterion "cyclespace  ambiguity" on support with a cycle
  (e.g., 22 chosen block or mixed chosen/nonchosen), compare with Section 16.227 (Q43.S105).

### 16.253. Exploratory step (toy computation): 22 chosen-loop allows possible forcing info and 1-bit ambiguity

- `Lens:` Invariant.
- `Statement (Q43.S105-cycle-space-criterion):`
  On a 44 grid, support from 22 chosencenters may support possible forcinginformation
  $J$, and closed $I$ on this support are exactly two (horizontal/vertical matching);
  both pass Def. 6.13(2), which means that 1bit of loop ambiguity is not eliminated by local
  conditions.
- `Toy test:`
  1) Take chosen centers $U=\\{(2,2),(2,3),(3,2),(3,3)\\}$ on 44, set $S=\\varnothing$,
     $I=\\varnothing$, $\\pi=\\varnothing$, and the branch $\\psi$ contains the variables associated
     with every $u\\in U$.
  2) Define $J^{H}$: two horizontal edges $(2,2)(2,3)$ and $(3,2)(3,3)$ plus non-edges in
     in all other directions for each $u\\in U$. Then $J^{H}$ is locally consistent and closed
     on each $u$ (odddegree=1; Def. 5.8/5.11:
     `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1618-1623,1659-1665`),
     therefore Def. 6.2(1-2) are fulfilled (`…:1882-1888`). By Def. 5.9 information in all 4 directions
     each $u$ forces variables to $\\psi$ (`…:1632-1636`), and removing any piece breaks
     forcedness means Def. 6.2(3) and the minimality is satisfied. Def. 6.2(4) is trivial (non-chosen).
  3) Similar to $J^{V}$ with two vertical edges - also possible forcing information.
  4) For a fixed support $U$, closed information sets correspond to odd numbers
     subgraphs of the 4cycle; the only solutions are $J^{H}$ and $J^{V}$ (see Section 16.227). In each case,
     taking $I:=J$, we get a locally consistent assignment on the chosen paths, so that
     Def. 6.13(2) does not give rise to conflict (`…:2359-2367`).
- `Status:` proven (the support loop is implementable, and exactly 1 bit of ambiguity remains).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` generalize the criterion through $\\mathbb F_2$-rank/quotient-graph for a fixed
  pairing $\\pi$ (Q43.S106).

### 16.254. Research step (proof): $\\pi$quotient is reduced to the cyclespace chosenpart

- `Lens:` Communication/Rank.
- `Statement (Q43.S106-pi-quotient-rank-lemma):`
  Let us fix support $U$ and pairing $\\pi$. Let $I$ be a closed information set on $U$,
  compatible with $\\pi$ in the sense of Invariant 6.1(4)/Def. 6.2(4), and $I$ does not contain
  chosen-non-chosen edges (Remark after Invariant 6.1). Let us denote by $G_{\\mathrm{ch}}$
  graph of possible edges on chosen centers from $U$. Then the set of such $I$ forms
  affine $\\mathbb F_2$ subspace of dimension $\\beta(G_{\\mathrm{ch}})$; in particular
  $$|\\{I\\}|=2^{\\beta(G_{\\mathrm{ch}})}.$$
  If we define $G/\\pi$ as the graph obtained by contracting the components of $\\pi$ inside $U$,
  then from the absence of selected-unselected edges it follows $\\beta(G/\\pi)=\\beta(G_{\\mathrm{ch}})$,
  and the formula coincides with the "$\\pi$quotient" criterion.
- `Proof:`
  1) According to Invariant 6.1(4) and Remark after Def. 5.11, on non-chosen centers $I$ represents
     is the union of integer components $\\pi$, each of which is itself closed
     information set. Consequently, the structure of $I$ on non-chosen is fixed by the chosen
     components of $\\pi$ and does not give degrees of freedom.
  2) According to Remark, after Invariant 6.1 in $I$ there are no paths between chosen and non-chosen centers,
     This means that the edges $I$ are decomposed into the "chosen" and "non-chosen" components.
  3) On the chosen-part, closedness is equivalent to the condition "odd-degree on each center", so
     that the set of solutions is exactly an affine space of odd subgraphs
     $G_{\\mathrm{ch}}$ and has size $2^{\\beta(G_{\\mathrm{ch}})}$ (see Section 16.227).
  4) Contraction of components $\\pi$ does not affect the cycle-space of the chosen-part (components
     $\\pi$ are isolated), so $\\beta(G/\\pi)=\\beta(G_{\\mathrm{ch}})$.
- `Toy test:`
  1) 22 chosen cycle from Section 16.253: $\\pi=\\varnothing$, $G/\\pi=G$, $\\beta=1$  two $I$
     (horizontal/vertical matching).
  2) Two adjacent chosen from Section 16.252: $\\pi=\\varnothing$, $G/\\pi$ is a tree, $\\beta=0$ 
     $I$ is unique.
- `Status:` proven (in the canonical mode $\\pi$ fixes the nonchosen parts, and the ambiguity
  is entirely specified by the cyclespace of the chosengraph).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` find (or exclude) an example where $\\beta(G/\\pi)=1$,
  but Def. 6.2(4) prohibits all closed $I$ (Q43.S107-pi-quotient-counterexample-def6-2-4).

### 16.255. Research step (toy computation): 22 chosen-cycle + -component of 2 non-chosen

- `Lens:` Invariant.
- `Statement (Q43.S107-pi-quotient-counterexample-def6-2-4):`
  In the minimal configuration "22 chosencycle + one nonchosen component from two neighboring ones
  centers" with the prohibition of chosen-non-chosen edges (Def. 6.2(4)) mod-2 the system on the edges is consistent,
  those. closed $I$ exist despite $\\beta(G/\\pi)=1$.
- `Toy test:`
  1) Take chosencenters $C=\\{(2,2),(2,3),(3,2),(3,3)\\}$ (4cycle) and nonchosen
     $N=\\{(2,4),(3,4)\\}$, vertically adjacent. Let pairing $\\pi$ have one component
     $P$ on $N$ with edge $f=(2,4)(3,4)$, and $U=C\\cup N$ is support. By Def. 6.2(4) and remark
     “no chosen–non‑chosen edge” (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1882-1893`)
     the directions between $(2,3)$-$(2,4)$ and $(3,3)$-$(3,4)$ are fixed as non-edges.
  2) Let us denote the edges of the chosen cycle:
     $e_1=(2,2)(2,3)$, $e_2=(2,3)(3,3)$, $e_3=(3,3)(3,2)$, $e_4=(3,2)(2,2)$ and the variable $y$
     for $f$. Closedness (Def. 5.8/5.11: `…:1618-1623,1659-1665`) gives the equations
     $e_1+e_4=1$, $e_1+e_2=1$, $e_2+e_3=1$, $e_3+e_4=1$ on chosen vertices and $y=1$ on $N$.
  3) The system has exactly two solutions on $C$ (horizontal or vertical matching) and
     fixes $y=1$; this means closed $I$ exists and a "bottleneck" Def. 6.2(4) in this
     There is no minimum configuration. When contracting $\\pi$, the cyclespace of the chosenpart
     does not change, so $\\beta(G/\\pi)=\\beta(C)=1$.
- `Status:` toy computation (Def. 6.2(4) conflict not found in minimal configuration).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether a -component of odd size (or two components) can
  under the condition "$J$ is closed for nonchosen" (Def. 6.2(2)+(4)), exclude all $I$ under
  $\\beta(G/\\pi)=1$; or try to prove the general lemma about chosen/non-chosen decoupling.

### 16.256. Exploratory step (toy computation): odd -component non-chosen

- `Lens:` Invariant.
- `Statement (Q43.S108-odd-pi-component-parity):`
  if the non-chosen -component has an odd size and Def. 6.2(2)+(4) requires that $J$
  was closed at all its centers with the prohibition of chosen-non-chosen edges, then the mod-2 system
  closedness is inconsistent and closed $I$ does not exist. However, according to Def. 5.2  components
  have size 2 or 4, so such obstruction is not implemented in real .
- `Toy test:`
  1) Let chosen-centers $C=\\{(2,2),(2,3),(3,2),(3,3)\\}$ (22 cycle), and non-chosen
     $N=\\{(2,4),(3,4),(4,4)\\}$ form one -component $P$ with edges
     $f_1=(2,4)(3,4)$, $f_2=(3,4)(4,4)$. By Def. 6.2(4) selected-unselected edges are prohibited.
  2) Closure to $N$ (Def. 5.11: `…:1659-1665`) gives the equations $f_1=1$, $f_1+f_2=1$,
     $f_2=1$; summation gives $0=1$ modulo 2, i.e. there is no solution.
  3) Equivalently: in any graph component of odd size the system $A x=\\mathbf 1$
     is inconsistent, since the sum of all equations is 0, and the right side is 1.
  4) Part $C$ still has two solutions (matching), but the odd component $N$ prohibits
     all closed $I$.
- `Status:` toy computation (parity conflict for odd component; outside the  model).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether two  components (even even ones) can give a similar
  incompatibility at $\\beta(G/\\pi)=1$ (Q43.S109).

### 16.257. Exploratory step (toy computation): two even -components non-chosen

- `Lens:` Communication/Rank.
- `Statement (Q43.S109-two-pi-components-rank):`
  in the configuration "22 chosencycle + two disjoint components of size 2" when prohibited
  chosen-non-chosen edges (Def. 6.2(4)) mod-2 closedness system is consistent; closed $I$
  exist despite $\\beta(G/\\pi)=1$.
- `Toy test:`
  1) Take chosencenters $C=\\{(2,2),(2,3),(3,2),(3,3)\\}$ (4cycle) and two nonchosen pairs
     $N_1=\\{(2,4),(3,4)\\}$, $N_2=\\{(4,2),(4,3)\\}$. Let pairing $\\pi$ have two components
     $P_1$ with edge $f_1=(2,4)(3,4)$ and $P_2$ with edge $f_2=(4,2)(4,3)$; $U=C\\cup N_1\\cup N_2$.
     By Def. 6.2(4) and the remark "no chosen-non-chosen edge" of the direction between chosen and non-chosen
     are recorded as non-edges.
  2) For the chosen cycle we denote $e_1=(2,2)(2,3)$, $e_2=(2,3)(3,3)$, $e_3=(3,3)(3,2)$,
     $e_4=(3,2)(2,2)$. Closedness (Def. 5.8/5.11: `…:1618-1623,1659-1665`) gives
     $e_1+e_4=1$, $e_1+e_2=1$, $e_2+e_3=1$, $e_3+e_4=1$ on $C$.
  3) On non-chosen pairs we obtain the equations $f_1=1$ and $f_2=1$ (each center has degree 1
     inside its component). These restrictions are independent of the chosen part.
  4) The system is consistent: equations on $C$ give two solutions (horizontal/vertical matching),
     and $f_1=f_2=1$ are fixed uniquely. By contracting $\\pi$ we obtain a 4cycle and two isolated
     vertices, so $\\beta(G/\\pi)=1$.
- `Status:` toy computation (two even  components do not create a new incompatibility).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check configurations with -components of size 4 or try to prove
  general lemma on chosen/non-chosen decoupling (Q43.S110).

### 16.258. Exploratory step (toy computation): even -component-star and decoupling

- `Lens:` Invariant.
- `Statement (Q43.S110-decouple-even-pi):`
  In canonical mode (Invariant 6.1(4) + chosen-non-chosen edges ban) configuration
  "22 chosen-cycle + -component-edge (|P|=2) + -component-star (|P|=4)" gives a joint
  system $A x=\\mathbf 1$; the nonchosen part is fixed, and the number of closed $I$ is equal to
  $2^{\\beta(G_{\\mathrm{ch}})}$ (here $=2$).
- `Toy test:`
  1) Take chosen-centers $C=\\{(2,2),(2,3),(3,2),(3,3)\\}$ (22 cycle) and a non-chosen pair
     $N_2=\\{(2,6),(3,6)\\}$ with edge $f$ (-component-edge). For the second -component we take
     star $N_4=\\{(5,5),(5,4),(5,6),(6,5)\\}$ with edges $g_1=(5,5)(5,4)$,
     $g_2=(5,5)(5,6)$, $g_3=(5,5)(6,5)$ (Def. 5.2: components  - edge or star of size 4,
     `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1442-1449`).
     The components are separated from $C$, so there are no chosen-non-chosen edges (Def. 6.2(4)).
  2) On the chosen cycle the equations are the same as in Section 16.255: $e_1+e_4=1$, $e_1+e_2=1$,
     $e_2+e_3=1$, $e_3+e_4=1$, hence two solutions (H/V matching).
  3) On the edge $f$, closure gives $f=1$.
  4) On the star, the leaves give $g_1=g_2=g_3=1$, and at the central node $g_1+g_2+g_3=1$,
     what is shared; the only solution.
  5) Result: the non-chosen part is fixed, and the chosen part gives 2 solutions; That's why
     $|\\{I\\}|=2=2^{\\beta(G_{\\mathrm{ch}})}$ (since $\\beta(G_{\\mathrm{ch}})=1$).
- `Status:` toy computation (even -star component does not add restrictions; decoupling is preserved).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether two size 4 -component stars can produce
  incompatibility at $\\beta(G/\\pi)=1$ (Q43.S111-size4-pi-obstruction).

### 16.259. Exploratory step (toy computation): two -stars of size 4 do not give parity obstruction

- `Lens:` Invariant.
- `Statement (Q43.S111-size4-pi-obstruction):`
  in the minimal configuration "22 chosen-cycle + two disjoint -stars of size 4"
  under the ban chosen-non-chosen edges mod-2, the closedness system is consistent; parity
  there is no obstruction.
- `Toy test:`
  1) Let chosen centers $C=\\{(2,2),(2,3),(3,2),(3,3)\\}$ (22 cycle). Let's take two disjoint
     -components of size 4 stars: $N_4^a=\\{(5,5),(5,4),(5,6),(6,5)\\}$ with edges
     $g_1=(5.5)(5.4)$, $g_2=(5.5)(5.6)$, $g_3=(5.5)(6.5)$ and
     $N_4^b=\\{(7,2),(7,1),(7,3),(8,2)\\}$ with edges
     $h_1=(7,2)(7,1)$, $h_2=(7,2)(7,3)$, $h_3=(7,2)(8,2)$.
     The components are removed from $C$, so there are no chosen-non-chosen edges (Def. 6.2(4)).
  2) For the chosen cycle we denote $e_1=(2,2)(2,3)$, $e_2=(2,3)(3,3)$, $e_3=(3,3)(3,2)$,
     $e_4=(3,2)(2,2)$. Closedness gives the same equations $e_1+e_4=1$, $e_1+e_2=1$,
     $e_2+e_3=1$, $e_3+e_4=1$, so there are two solutions (H/V matching).
  3) On each -star the leaves give $g_1=g_2=g_3=1$ and $h_1=h_2=h_3=1$, and at the central nodes
     $g_1+g_2+g_3=1$ and $h_1+h_2+h_3=1$; this is joint, because $1+1+1\\equiv 1\\pmod 2$.
     The solution to the non-chosen part is the only one.
  4) Result: the system $A x=\\mathbf 1$ breaks up into blocks of chosen/stars and is consistent; number
     closed $I$ is equal to $2^{\\beta(G_{\\mathrm{ch}})}=2$.
- `Status:` toy computation (counterexample: two size 4  stars do not create an obstruction).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to generalize the compatibility for two -stars or derive
  parity criterion via $G/\\pi$ (Q43.S112-size4-pi-compatibility).

### 16.260. Exploratory step (toy computation): =0 does not give conflict for two -stars

- `Lens:` Model stress test.
- `Statement (Q43.S113-beta0-counterexample):`
  There is a configuration of two -stars of size 4 without chosen-non-chosen edges, for which
  $\\beta(G/\\pi)=0$, but the system $A x=\\mathbf 1$ is inconsistent.
- `Toy test:`
  1) In the absence of chosen-non-chosen edges Def. 6.2(4) fixes the non-chosen part as
     union of components $\\pi$, i.e. graph of possible edges on non-chosen - disjoint
     the sum of two -stars.
  2) For one star with center $v$ and leaves $u_1,u_2,u_3$, closure gives the equations
     $x_{vu_i}=1$ for each $i$ and $x_{vu_1}+x_{vu_2}+x_{vu_3}=1$, which is joint; solution
     unique: all three edges are equal to 1.
  3) Consequently, for two -stars the system $A x=\\mathbf 1$ splits into two independent
     block and always joint; $\\beta(G/\\pi)=0$ (each star is a tree).
  4) Brute force check of all disjoint pairs of  stars in 44 and 55 lattices: 68 and 564 pairs
     Accordingly, no incompatible cases were found.
- `Status:` no counterexample was found (=0 does not lead to a conflict in the "two -stars" model).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to formalize a general compatibility criterion for two -stars
  (Q43.S112-size4-pi-compatibility).

### 16.261. Research step (proof): parity criterion via quotient

- `Lens:` Equivalence.
- `Statement (Q43.S115-quotient-parity-criterion):`
  In canonical mode (Invariant 6.1(4) + chosen-non-chosen edges ban), the system
  closedness of $A x=\\mathbf 1$ on support $U$ is equivalent in the existence of solutions to the system
  $B_{G/\\pi}x=b$ on the graph $G/\\pi$, where $B_{G/\\pi}$ is the incidence matrix, and
  $b\\equiv \\mathbf 1$ on the vertices. Therefore, a solution exists if and only if
  when in each connected component $H$ of the graph $G/\\pi$ the following holds:
  $\\sum_{v\\in H} b_v\\equiv 0$ (i.e. $|V(H)|$ is even; equivalent to $b\\perp\\ker B_{G/\\pi}^T$).
- `Proof:`
  1) From the chosen-non-chosen edges prohibition, the graph of possible edges is decomposed into
     $G_{\\mathrm{ch}}$ and isolated components $\\pi$; therefore $A$ is block diagonal:
     $A=A_{\\mathrm{ch}}\\oplus\\bigoplus_{P\\in\\pi}A_P$.
  2) For each component $P$ only |P|=2 (edge) or |P|=4 (star) are allowed (Def. 5.2).
     In both cases, the system $A_P x=\\mathbf 1$ has a unique solution (see Section 16.256, Section 16.258),
     this means that the compatibility $A x=\\mathbf 1$ is equivalent to the compatibility $A_{\\mathrm{ch}}x=\\mathbf 1$.
  3) Since the components of $\\pi$ are isolated, $G/\\pi$ coincides with $G_{\\mathrm{ch}}$ plus isolated
     tops; hence $A_{\\mathrm{ch}}=B_{G/\\pi}$ and $b\\equiv\\mathbf 1$.
  4) For any component $H$, the matrix $B_H$ has rank $|V(H)|-1$, and the sum of the rows is zero,
     therefore $B_H x=b_H$ is consistent iff $\\sum_{v\\in H} b_v=0$; this is equivalent to the condition
     $b\\perp\\ker B_{G/\\pi}^T$.
- `Toy test:`
  1) 22 chosencycle and adjacent chosen (sections Section 16.252-Section 16.253): $|V|$ is even  the system is consistent.
  2) Adding -components of size 2 or 4 (Section 16.255-Section 16.259) does not change the condition: each
     component $H$ has an even size  compatibility is preserved.
  3) The hypothetical odd -component (Section 16.256) gives $|V(H)|$ odd  inconsistency.
- `Status:` proven (compatibility reduces to the evenness of the components in $G/\\pi$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` stress test the criterion outside the canonical mode
  (overlapping -stars / chosen-non-chosen edge) and try to find a counterexample
  (Q43.S116-overlapping-stars-counterexample).

### 16.262. Exploratory step (counterexample): overlapping -stars break decoupling

- `Lens:` Model stress test.
- `Statement (Q43.S116-overlapping-stars-counterexample):`
  Outside the canonical regime (allowing overlap of -stars) parity criterion Section 16.261
  in the naive form "each star has an even size  Ax=\\mathbf 1 is compatible"
  incorrect: there exists support $U$, where each of the two -stars is of size 4, but the system
  $A x=\\mathbf 1$ is inconsistent.
- `Counterexample (4x4):`
  1) Let all centers be non-chosen. Let's take $U=\\{(2,2),(2,1),(2,3),(1,2),(3,2)\\}$.
     Let us define two -stars with a common center $c=(2,2)$:
     $P_1$ on edges $c(2,1),c(1,2),c(2,3)$ and $P_2$ on edges $c(2,1),c(2,3),c(3,2)$.
     This is prohibited Def. 5.2 (component overlap), but allowed outside of canonical mode.
  2) If we ignore overlap and apply the Section 16.261 "over  components" criterion,
     each star has 4 vertices (even), so the parity test does not rule out a solution.
  3) Let us denote the edges $e_W=c(2,1)$, $e_E=c(2,3)$, $e_N=c(1,2)$, $e_S=c(3,2)$.
     The linear closed system (Def. 5.8/5.11) gives on the leaves $e_W=e_E=e_N=e_S=1$,
     and at the center $e_W+e_E+e_N+e_S=1$. Substitution gives $0=1$, i.e. $A x=\\mathbf 1$ is inconsistent.
- `Status:` counterexample (overlapping -stars breaks decoupling on $U$).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check chosen-non-chosen edge as a source of conflict in canonical
  criteria (Q43.S117-chosen-nonchosen-edge-counterexample).

### 16.263. Exploratory step (counterexample): one chosen-non-chosen edge breaks the $G/\pi$ criterion

- `Lens:` Model stress test.
- `Statement (Q43.S117-chosen-nonchosen-edge-counterexample):`
  There is a canonical $\\pi$ (one star of size 4) and a locally consistent $J$ with exactly
  one chosen-non-chosen edge, for which the parity criterion Section 16.261 on $G/\\pi$
  predicts compatibility, but the closed system $A x=\\mathbf 1$ is inconsistent.
- `Counterexample (4x4):`
  1) Take a non-chosen -star $P$ with center $v_0=(2,2)$ and leaves
     $v_W=(2,1)$, $v_N=(1,2)$, $v_E=(2,3)$; component $\\pi$ - edges
     $g_W=v_0v_W$, $g_N=v_0v_N$, $g_E=v_0v_E$. Let the chosen center $c=(3,1)$ be adjacent to $v_W$,
     and $J$ contains edges $g_W,g_N,g_E$ and a single mixed edge $m=cv_W$;
     There are no other information pieces. Then $J$ is locally consistent (at no center
     no information in all 4 directions).
  2) Any closed information set $I$, pairwiselocally consistent with $J$, adds
     non-edges in missing directions, so the system of closure on $U$ has the form:
     $$m=1,\\quad g_N=1,\\quad g_E=1,\\quad g_W+m=1,\\quad g_W+g_N+g_E=1.$$
     From $m=1$ we obtain $g_W=0$ (equation for $v_W$), but from $g_N=g_E=1$ it follows
     $g_W=1$ (equation for $v_0$). This is a contradiction, which means $A x=\\mathbf 1$ is inconsistent.
  3) At the same time, the graph $G/\\pi$ is obtained by contracting the star $P$ into one vertex $p$;
     there remain two vertices $\\{p,c\\}$ and one edge between them, i.e. component has an even
     size and Section 16.261 parity criterion predict compatibility.
- `Status:` counterexample (one mixed-edge breaks the $G/\\pi$ criterion).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` try to restore the criterion by adding a correction for the mixed edge
  (for example, derive a condition for the parity of incident edges of a -star or show that
  any mixed-edge gives a conflict when closed).

### 16.264. Research step (proof): parity invariant for mixed-edges of the -component

- `Lens:` Invariant.
- `Statement (Q43.S118-mixed-edge-parity-invariant):`
  Let $I$ be a closed information set on support $U$ with pairing $\\pi$, and the closedness system
  on the edges $I$ has the form $A x=\\mathbf 1$ (odddegree at each center). For anyone
  We denote the -components of $P$ by $\\delta_{\\mathrm{mix}}(P)$ as the number of mixed-edges,
  incident $P$ (edges between $P$ and chosen centers with $x_e=1$). Then
  $$\\delta_{\\mathrm{mix}}(P)\\equiv \\sum_{v\\in P}1\\pmod 2,$$
  those. mixed-edges parity is equal to the sum of "charges" on $P$. In particular, since
  $|P|\\in\\{2,4\\}$, for any realizable configuration $\\delta_{\\mathrm{mix}}(P)$ is even.
- `Proof:`
  1) For each $v\\in P$ the equation $A x=\\mathbf 1$ gives
     $\\sum_{e\\ni v} x_e=1$.
  2) Adding these equations over all $v\\in P$, we get
     $\\sum_{e\\in E(P)}2x_e+\\sum_{e\\in\\partial P}x_e=|P|$.
     The internal edges of $E(P)$ disappear modulo 2, leaving only the edges
     $\\partial P$, incident $P$ and leaving it.
  3) All edges from $\\partial P$ are exactly mixed-edges (between $P$ and chosen-centers), therefore
     $\\sum_{e\\in\\partial P}x_e=\\delta_{\\mathrm{mix}}(P)$, which gives the required congruence.
- `Toy test:`
  1) 44 -star $P$ as in Section 16.263: center $v_0=(2,2)$ and leaves
     $v_W=(2,1)$, $v_N=(1,2)$, $v_E=(2,3)$, one chosen-center $c=(3,1)$ and mixed-edge
     $m=cv_W$. Then $|P|=4$  $\\delta_{\\mathrm{mix}}(P)\\equiv 0$, but $c$ has only one
     incident edge gives $m=1$, a contradiction. This explains the conflict in Section 16.263.
  2) Add a second chosen center $c'=(1,1)$ and a mixed edge $m'=c'v_N$.
     The assignment $m=m'=1$, $g_E=1$, $g_W=g_N=0$ satisfies the equations
     $g_W+m=1$, $g_N+m'=1$, $g_E=1$, $g_W+g_N+g_E=1$, so $A x=\\mathbf 1$ is consistent.
     The parity $\\delta_{\\mathrm{mix}}(P)=2$ coincides with $|P|\\equiv 0$.
- `Status:` proven (parity of mixed-edges on each -component is a necessary condition).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check whether mixed-edges parity provides a sufficient criterion
  (or find the minimal obstructive motif/canonical swap in a -star)
  (Q43.S119).

### 16.265. Exploratory step (counterexample): mixed-edges parity is insufficient

- `Lens:` Model stress test.
- `Statement (Q43.S120-even-mixed-edge-counterexample):`
  Even if each -component has an even number of mixed-edges, the closed system
  $A x=\\mathbf 1$ may be inconsistent: a -star of size 4 is sufficient, where
  two mixed-edges are incident to one chosen-center.
- `Counterexample (4x4):`
  1) Non-chosen -star $P$ with center $v_0=(2,2)$ and leaves
     $v_W=(2,1)$, $v_N=(1,2)$, $v_E=(2,3)$. Component $\\pi$ - edges
     $g_W=v_0v_W$, $g_N=v_0v_N$, $g_E=v_0v_E$ (Def. 5.2).
  2) One chosen center $c=(1,1)$ is adjacent to $v_W,v_N$; add two mixed edges
     $m_W=cv_W$, $m_N=cv_N$, no other edges. Then
     $\\delta_{\\mathrm{mix}}(P)=2$ and $|P|=4$ (Section 16.264 parity satisfied).
  3) Equations $A x=\\mathbf 1$ on $U=\\{v_0,v_W,v_N,v_E,c\\}$:
     $$g_E=1,\\quad g_W+m_W=1,\\quad g_N+m_N=1,\\quad
     g_W+g_N+g_E=1,\\quad m_W+m_N=1.$$
     From $g_E=1$ we get $g_W+g_N=0$, which means $m_W=m_N=1+g_W$, and then
     $m_W+m_N=0$, a contradiction.
- `Status:` counterexample (mixed-edges parity on the -component is not sufficient).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check the criterion on the quota, saving the chosen vertices
  (for example, $b_{\\mathrm{mix}}\\perp\\ker B_{G/\\pi}^T$) and check with toy cases
  §16.263–§16.265 (Q43.S121).

### 16.266. Research step (toy computation): mixed-edge criterion on quota

- `Lens:` Invariant.
- `Statement (Q43.S121-mixed-edge-quotient-linear-criterion):`
  Conjecture: if $G/\\pi$ is obtained by contracting each non-chosen -component, and the chosen vertex
  are left, and $b_{\\mathrm{mix}}(v)=1$ for chosen vertices, $b_{\\mathrm{mix}}(P)\\equiv|P|\\pmod 2$
  for contracted -components, then the compatibility of $A x=\\mathbf 1$ requires
  $b_{\\mathrm{mix}}\\perp\\ker B_{G/\\pi}^T$ (equivalent to the existence of a solution
  $B_{G/\\pi}x=b_{\\mathrm{mix}}$). Toy test: Section 16.265 configuration violates this condition.
- `Toy test:`
  1) In Section 16.265 there is a -star $P$ of size 4 and a chosen center $c$ incident to two mixed edges.
     In $G/\\pi$ we obtain two vertices $\\{p,c\\}$ and two parallel arcs $pc$.
  2) The incidence matrix $B_{G/\\pi}$ over $\\mathbb F_2$ has two identical columns
     $(1,1)^T$, means $\\ker B_{G/\\pi}^T=\\langle(1,1)\\rangle$.
  3) Here $b_{\\mathrm{mix}}(c)=1$ and $b_{\\mathrm{mix}}(p)=|P|\\equiv 0$, therefore
     $b_{\\mathrm{mix}}\\cdot(1,1)=1$, and the condition $b_{\\mathrm{mix}}\\perp\\ker B_{G/\\pi}^T$
     is not executed.
- `Status:` partially (toy test supports criterion; Section 16.265 is eliminated).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` or prove the equivalence $A x=\\mathbf 1\\Leftrightarrow B_{G/\\pi}x=b_{\\mathrm{mix}}$
  in canonical mode, or find a counterexample where the condition is satisfied, but $A x=\\mathbf 1$
  incompatible (Q43.S122).

### 16.267. Research step (proof): quota criterion with $b_{\\mathrm{mix}}$ is sufficient

- `Lens:` Equivalence.
- `Statement (Q43.S122-quotient-sufficiency-proof):`
  In canonical mode (Invariant 6.1(4): non-chosen centers are divided into -components)
  a closed system $A x=\\mathbf 1$ on support $U$ is consistent if and only if
  when there is a solution $y$ to the equation $B_{G/\\pi}y=b_{\\mathrm{mix}}$, where $G/\\pi$ is
  the graph after contraction is a -component, and $b_{\\mathrm{mix}}(c)=1$ for chosen-centers and
  $b_{\\mathrm{mix}}(P)\\equiv|P|\\pmod 2$ for the component vertex $P$.
- `Proof:`
  1) Divide the edges of $G$ into $E_{cc}$ (chosen-chosen), $E_{\\mathrm{mix}}$ (chosen-non-chosen)
     and $E_P$ inside each -component of $P$. Equations $A x=\\mathbf 1$ on chosencenters
     use only $E_{cc}\\cup E_{\\mathrm{mix}}$ and match strings
     $B_{G/\\pi}y=b_{\\mathrm{mix}}$ for $y:=x|_{E_{cc}\\cup E_{\\mathrm{mix}}}$.
  2) For each -component $P$ we set
     $m_P(v):=\\sum_{e\\in E_{\\mathrm{mix}}: e\\ni v} y_e$ for $v\\in P$. Then the equations
     on $P$ have the form $B_{H_P}x_P=\\mathbf 1+m_P$, where $H_P=(P,E_P)$.
  3) Adding over $v\\in P$, we obtain $0=\\sum_{v\\in P}(1+m_P(v))$, i.e.
     $\\delta_{\\mathrm{mix}}(P)\\equiv|P|\\pmod 2$. This is exactly a line
     $B_{G/\\pi}y=b_{\\mathrm{mix}}$ for vertex $P$.
  4) Conversely, if $y$ satisfies $B_{G/\\pi}y=b_{\\mathrm{mix}}$, then for each $P$
     the vector $\\mathbf 1+m_P$ has an even sum, which means it lies in the image of $B_{H_P}$.
     For an $H_P$-tree (edge or 4star), the solution $x_P$ is unique (by leaves); All in all
     This parity is enough for the graph. Gluing together solutions for all $P$ and taking
     $x|_{E_{cc}\\cup E_{\\mathrm{mix}}}=y$, we obtain the solution $A x=\\mathbf 1$.
- `Toy test:`
  -component $P$ -- 4-cycle $v_1v_2v_3v_4v_1$ with two boundary vertices $v_1,v_3$
  and mixed-edges $m_1,m_3$ to chosen-centers. Equations:
  $x_{12}+x_{14}+m_1=1$, $x_{12}+x_{23}=1$, $x_{23}+x_{34}+m_3=1$,
  $x_{34}+x_{14}=1$. The sum gives $m_1+m_3=0$ (|P|=4). For $m_1=m_3$ we take $x_{12}=t$,
  we get $x_{23}=1+t$, $x_{34}=t+m_3$, $x_{14}=1+t+m_1$, so a solution exists
  for any $t$.
- `Status:` proven (the quota criterion with $b_{\\mathrm{mix}}$ is necessary and sufficient).
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` stress test a criterion outside the canonical mode (for example, allow
  overlap components or additional nonchosen-nonchosen edges) and check
  what additional linear constraints appear (Q43.S123).

### 16.268. Exploratory step (toy computation): extra non-chosen edge between two -stars

- `Lens:` Invariant.
- `Statement (Q43.S124-extra-nn-edge-constraint):`
  In a configuration of two size 4 disjoint -stars and one extra non-chosen edge between them
  system $A x=\\mathbf 1$ is consistent if and only if there is an edge in quotient $G/\\pi$
  between components has the value 0; this is exactly the condition $B_{G/\\pi}x=b_{\\mathrm{mix}}$
  (where $b_{\\mathrm{mix}}$ is zero, because $|P|=|Q|=4$).
- `Toy test:`
  1) Let both -components be non-chosen: $P=\\{a_0,a_1,a_2,a_3\\}$, $Q=\\{b_0,b_1,b_2,b_3\\}$
     with stars $g_i=a_0a_i$ and $h_i=b_0b_i$ for $i=1,2,3$.
     Let's add extra edge $e=a_1b_1$ between the components; there are no other ribs.
  2) Equations $A x=\\mathbf 1$:
     $g_2=g_3=1$, $g_1+g_2+g_3=1$, $g_1+e=1$; similarly
     $h_2=h_3=1$, $h_1+h_2+h_3=1$, $h_1+e=1$.
     Hence $g_1=h_1=1$ and $e=0$.
  3) $G/\\pi$ has two vertices $p,q$ (we contract $P,Q$) and one edge $e$.
     Since $|P|=|Q|=4$, we have $b_{\\mathrm{mix}}(p)=b_{\\mathrm{mix}}(q)=0$, and
     $B_{G/\\pi}x=b_{\\mathrm{mix}}$ gives $e=0$.
- `Status:` partially (toy test shows that in this minimal case the additional edge
  is forced to zero and the criterion on the quota does not break).
- `StepID:` Q43.S124-extra-nn-edge-constraint.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` add a connection forming a cycle in $G/\\pi$ (for example, chosen vertex
  with two mixed edges between $P,Q$) and check whether a new linear condition appears
  over $B_{G/\\pi}x=b_{\\mathrm{mix}}$ (Q43.S125-quotient-cycle-test).

### 16.269. Exploratory step (toy computation): triangle in $G/\\pi$ with chosencenter

- `Lens:` Invariant.
- `Statement (Q43.S125-quotient-cycle-test):`
  In a configuration of two size 4 disjoint -stars, one extra non-chosen edge between
  them and one chosen center with two mixed edges to these components of the system
  $A x=\\mathbf 1$ is consistent if and only if there is a solution
  $B_{G/\\pi}x=b_{\\mathrm{mix}}$; in particular, in this minimal cycle both systems
  incompatible.
- `Toy test:`
  1) Let $P=\\{a_0,a_1,a_2,a_3\\}$, $Q=\\{b_0,b_1,b_2,b_3\\}$ be non-chosen -stars
     with star edges $g_i=a_0a_i$ and $h_i=b_0b_i$ for $i=1,2,3$.
     Add an extra edge $e=a_1b_1$ and a chosen center $c$ with mixed edges
     $m_P=ca_2$, $m_Q=cb_2$.
  2) The equations $A x=\\mathbf 1$ give
     $g_3=1$, $g_1+g_2+g_3=1$, $g_1+e=1$, $g_2+m_P=1$, whence $g_1=g_2$ and $e=m_P$;
     similarly $h_3=1$, $h_1+h_2+h_3=1$, $h_1+e=1$, $h_2+m_Q=1$, whence $e=m_Q$.
     At the chosen center $m_P+m_Q=1$, so $e=m_P=m_Q$ gives a contradiction.
  3) In $G/\\pi$ there are vertices $p,q,c$ and edges $e,m_P,m_Q$; vector
     $b_{\\mathrm{mix}}$ has $b(c)=1$, $b(p)=b(q)=0$, and
     $B_{G/\\pi}x=b_{\\mathrm{mix}}$ gives the system
     $m_P+m_Q=1$, $m_P+e=0$, $m_Q+e=0$, also inconsistent.
- `Status:` partially (toy test: the contradiction is already in $B_{G/\\pi}x=b_{\\mathrm{mix}}$; additional
  no restrictions beyond quotas were found).
- `StepID:` Q43.S125-quotient-cycle-test.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` stress test a cycle in $G/\\pi$ composed only of non-chosen
  -component (check whether $A x=\\mathbf 1$ allows non-zero nn-edges)
  (Q43.S126-quotient-cycle-nonchosen).

### 16.270. Exploratory step (counterexample): nn-cycle gives a 1-dimensional kernel

- `Lens:` Communication/Rank.
- `Statement (Q43.S127-cycle-rank-counterexample):`
  In a configuration without chosen centers, where $G/\\pi$ is a $k$ cycle of non-chosen  components
  size 2 and $b_{\\mathrm{mix}}=0$, the closed system $A x=\\mathbf 1$ admits
  non-zero assignment of nn-edges; at the quotation level it is a 1-dimensional core.
- `Toy test (k=4):`
  1) Let the -components $P_i=\\{a_i,b_i\\}$, $i=1,\\dots,4$, and internal edges
     $g_i=a_ib_i$. Let's add nn-edges $e_i=a_i a_{i+1}$ (indices modulo 4),
     there are no other ribs.
  2) Equations $A x=\\mathbf 1$: for $b_i$ we have $g_i=1$ (the only incident edge),
     and for $a_i$ $g_i+e_{i-1}+e_i=1$ is satisfied. Substitution gives
     $e_{i-1}+e_i=0$ for all $i$.
  3) Therefore $e_1=e_2=e_3=e_4$; the solution space is 1-dimensional, and a non-zero solution
     $e_i=1$ is acceptable (with $g_i=1$).
- `Status:` counterexample (nn-edges on a pure non-chosen cycle do not have to be zero).
- `StepID:` Q43.S127-cycle-rank-counterexample.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` check the feasibility of such a cycle on a lattice with Def. 6.2(1-4)
  (for example, a 3 or 4cycle of stars on 66) and whether there is a conflict in directions
  (Q43.S128-cycle-realizability-grid).

### 16.271. Exploratory step (proof): non-chosen cycle in $G/\pi$ is not implemented at Def. 6.2(1-4)

- `Lens:` Invariant.
- `Statement (Q43.S128-cycle-realizability-grid):`
  In canonical mode (Invariant 6.1(4) + Definition 6.2(4)) it is impossible to have
  nn-cycle composed of different non-chosen -components: any edges between
  by various components are fixed as non-edges, therefore in $G/\pi$ non-chosen
  the vertices are isolated.
- `Proof:`
  1) According to Invariant 6.1(4), part $I$ on non-chosen centers is a union of components
     pairing $\pi$ as closed information set (HR'22 `…:1857–1862`). Hence,
     $I$ does not contain edges between different -components.
  2) By Definition 6.2(4), the part $J$ at non-chosen centers is also a subset
     component $\pi$ in the form of closed information set (HR'22 `…:1888–1893`). Hence,
     $J$ does not contain edges between different components.
  3) For associated non-chosen centers that must be closed by Def. 6.2(2),
     all directions to centers outside their -component are fixed as non-edges.
     This means that nn-edges between components have a value of 0.
  4) Therefore, in the graph $G/\pi$ there are no edges between non-chosen vertices, and a cycle of such
     component is not possible. In particular, the design of Section 16.270 is not implemented on grid
     at Def. 6.2(1-4).
- `Status:` proven (the loop is not implemented in canonical mode).
- `StepID:` Q43.S128-cycle-realizability-grid.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` return to evaluation $A_1$: full percenter bit counting
  Algorithms 2-4 and explicit constant $A_1$ (Q43.S129-bound-a1-constant).

### 16.272. Exploratory step (exact citation): explicit $A_1$ has already been received

- `Lens:` Equivalence.
- `Statement (Q43.S129-bound-a1-constant):`
  The explicit constant $A_1$ for "constant-part" in Lemma 6.9 has already been calculated: $A_1^{\mathrm{tot}}=24$,
  and with separate accounting of signatures $A_1\le 15$.
- `Exact citation:` see Section 16.224 (Q43.S62-assemble-a1-sum) where the contributions of Algorithms 2-4 are summarized
  and signatures: $9+1+1+13=24$ bits per center; $A_1\le 15$ remains without signatures.
- `Status:` exact citation (S129 is closed with a link to an already proven step).
- `StepID:` Q43.S129-bound-a1-constant.
- `InfoGain:` 1.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` collect explicit constants in Lemma 6.9/4.2 from $A_1,A_2,A_3,A_4$ and
  check that the final parameter $A$ gives the correct recursion mode (Q43.S130-explicit-a-constant).

### 16.273. Exploratory step (proof): explicit $A$ in Lemma 6.9/4.2

- `Lens:` Trade-off.
- `Statement (Q43.S130-explicit-a-constant):`
  In Lemma 6.9 we can take an explicit constant $A\\le 668$ (for $t\\le s$), which means the same $A$
  also suitable for Lemma 4.2.
- `Proof:`
  In the proof of Lemma 6.9, the total number of **constant** bits, in addition to $a\\log t$ and $b\\log\\Delta$,
  consists of:
  1) $9|S^{*}_g|$ center signature bit;
  2) $A_1|S^{*}_g|$ bit "other centers" (HR'22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2538-2562`);
  3) $A_2|S^{*}_g|$ bits for the structure $J_j$ and $I^{*}_{-}$ (ibid.);
  4) $A_3 s$ bits from the stage/discovery counters, where $A_3$ is given by $s+16t+s/4$ (ibid.).
  According to Section 16.224 we have $9+A_1=A_1^{\\mathrm{tot}}=24$, according to Section 16.225 $A_2\\le 16$.
  In addition, from $|S^{*}_g|\\le s/4+16t$ and $t\\le s$ it follows $|S^{*}_g|\\le (65/4)s$, that is
  $A_4\\le 65/4$, and from $s+16t+s/4\\le (69/4)s$ it follows $A_3\\le 69/4$.
  Then
  $$A\\le A_3 + A_4(A_1^{\\mathrm{tot}}+A_2)=\\frac{69}{4}+\\frac{65}{4}\\cdot 40=\\frac{2669}{4}<668,$$
  so we can take $A:=668$.
  (If we use a rough estimate of $A_4\\le 69/4$, then $A\\le 708$.)
- `Status:` proven (explicit $A$).
- `StepID:` Q43.S130-explicit-a-constant.
- `InfoGain:` 1.
- `Barrier check:` r - applicable, NP - not applicable, alg - not applicable.
- `Next step:` compare conditions $n\\ge n_0(A)$ and $n\\ge 20 C n'\\log n'$ for $A=668$
  and note which one dominates in HR mode (Q43.S131-compare-n0-a).

### 16.274. Exploratory step (proof): comparison of $n_0(668)$ and $20 C n'\\log n'$

- `Lens:` Equivalence.
- `Statement (Q43.S131-compare-n0-a):`
  For $A=668$ we have $n_0(A)=2$, and for HR parameters ($C\\ge 3$, $t\\le s\\le n'/32$) the condition
  $n\\ge 20 C n'\\log n'$ automatically gives $n\\ge n_0(A)$. That is, the requirement $n\\ge n_0(A)$ is redundant.
- `Proof:`
  By Section 16.214 $n_0(A)=\\lceil e^{(48e^{1/2}/A)^{1/3}}\\rceil$. For $A=668$ we have
  $48e^{1/2}/668<1/8$, since $e^{1/2}<5/3$ (from the series $e^{1/2}$) and
  $48\\cdot(5/3)=80<668/8$. Then $(48e^{1/2}/668)^{1/3}<1/2$, whence
  $e^{(48e^{1/2}/668)^{1/3}}<e^{1/2}<2$, and the exponent is positive, which means $e^{\\cdot}>1$.
  Therefore, $n_0(668)=2$.
  Next, from $t,s,n'\\in\\mathbb N^+$ and $t\\le s\\le n'/32$ it follows $n'\\ge 32\\ge 2$.
  Therefore, for $C\\ge 3$ we have
  $$n\\ge 20 C n'\\log n'\\ge 20\\cdot 3\\cdot 2\\cdot (\\log 2)\\ge 20\\cdot 3\\cdot 2\\cdot \\frac12=60>2,$$
  where $\\log 2\\ge 1/2$ since $e^{1/2}<2$. This means $n\\ge n_0(668)$, and the condition $n\\ge n_0(A)$ is superfluous.
- `Toy test:` numerically $e^{(48e^{1/2}/668)^{1/3}}\\approx 1.634$, so $n_0(668)=2$;
  the minimum RHS for $C=3,n'=2$ gives $20\\cdot 3\\cdot 2\\log 2\\approx 83$.
- `Status:` proven (dominance of the condition $n\\ge 20 C n'\\log n'$).
- `StepID:` Q43.S131-compare-n0-a.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure arithmetic, no oracle involved).
  B) Natural proofs check: not applicable (no property of functions/lower bounds for circuits).
  C) Algebrization check: not applicable (no arithmetization/extension oracle).
- `Next step:` update summary Q43 (keep $n\\ge 20 C n'\\log n'$ as the only
  constraint on $n$) and check that other HR assumptions remain unchanged
  (Q43.S132-update-summary-dominant-bound).

### 16.275. Exploratory step (reduction/equivalence): summary of HR mode with dominant condition by $n$

- `Lens:` Compression/canonization.
- `Statement (Q43.S132-update-summary-dominant-bound):`
  In HR mode for Q43, you can leave the only $n$ limitation:
  $$n \\ge 20 C n' \\log n',$$
  since at $A=668$ the condition $n\\ge n_0(A)$ is automatically satisfied; other HR prerequisites
  (for example $C\\ge 3$, $t\\le s\\le n'/32$, $s\\ge 1$) do not change.
- `Rationale:`
  According to Section 16.274 $n_0(668)=2$. For $t,s,n'\\in\\mathbb N^+$ and $t\\le s\\le n'/32$ we have $n'\\ge 2$,
  therefore, for $C\\ge 3$ the minimum RHS $20 C n' \\log n'$ is strictly greater than 2. This means
  $n\\ge 20 C n'\\log n' \\Rightarrow n\\ge n_0(A)$.
- `Status:` reduction/equivalence (compression of the list of HR prerequisites).
- `StepID:` Q43.S132-update-summary-dominant-bound.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure arithmetic, no oracle involved).
  B) Natural proofs check: not applicable (no property of functions/lower bounds for circuits).
  C) Algebrization check: not applicable (no arithmetization/extension oracle).
- `Next step:` check that other HR prerequisites (conditions on $t',s,\\Delta$)
  remain compatible after replacing $t\\mapsto(2s+1)t$ (Q43.S133-hr-compatibility-check).

### 16.276. Research step (reduction/equivalence): compatibility of HR premises after $t\\mapsto(2s+1)t$

- `Lens:` Trade-off.
- `Statement (Q43.S133-hr-compatibility-check):`
  In HR mode for flat local-EF(s), with $M=\\mathrm{poly}(n)$ and $s=\\mathrm{polylog}(n)$,
  the remaining premises of Lemma 4.4/4.5 (in particular $t'\\le s_\\eta\\le n'/32$ and
  $t'(d)\\le n_d/16$) remain compatible after replacement
  $$t'=(2s+1)\\log M.$$
  Equivalently, it suffices to check that $t'=\\log^{O(1)}n$, and HR recursion gives
  $n_\\eta\\ge n/\\mathrm{polylog}(n)^\\eta$ at $\\eta\\le d$.
- `Rationale:`
  For $M=\\mathrm{poly}(n)$ and $s=\\mathrm{polylog}(n)$ we have $t'=(2s+1)\\log M=\\log^{O(1)}n$.
  In HR, the recursion $n_\\eta=\\lfloor n_{\\eta-1}/(A t'\\log^{c_1} n_{\\eta-1})\\rfloor$ gives
  $n_\\eta\\ge n/(A t'\\log^{c_1}n)^\\eta$. For $d=O(\\log n/\\log\\log n)$ the denominator is
  $\\mathrm{polylog}(n)^d=n^{o(1)}$, so $n_\\eta=n^{1-o(1)}$ and therefore
  $t'(d)\\le n_d/16$ for sufficiently large $n$.
  The condition $t'\\le s_\\eta$ is achieved by choosing $s_1:=\\max\\{\\log N,t'\\}$ and $s_\\eta=2^{\\eta-1}s_1$
  (this only changes the polylog factor in the HR proof); for $n$ large enough
  $s_\\eta\\le n'/32$ also remains.
- `Toy test:` take $n=2^{60}$, $n'=2^{20}$, $M=n^2$, $s=\\log n$.
  Then $t'\\approx (2\\cdot 41+1)\\cdot(2\\cdot 41)\\approx 6800$,
  $\\log^4 n\\approx 3\\cdot 10^6$, and $A t'\\log^4 n\\ll n/n'=2^{40}\\approx 10^{12}$,
  so $n/n'\\ge A t'\\log^{4} n$ is compatible; also $t'\\ll n_d$ and $t'\\le s_1$.
- `Status:` reduction/equivalence (compatibility of remaining conditions).
- `StepID:` Q43.S133-hr-compatibility-check.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure parameter estimates, the oracle is not involved).
  B) Natural proofs check: not applicable (no property of functions/lower bounds for circuits).
  C) Algebrization check: not applicable (no arithmetization/extension oracle).
- `Next step:` check where exactly $s_1=\\log N$ is used in HR Lemma 4.5
  (can it be formally replaced by $\\max\\{\\log N,t'\\}$ without hidden side effects),
  or fix the point of failure (Q43.S134-s1-swap-compatibility).

### 16.277. Research step (reduction/equivalence): replacing $s_1=\\log N$ with $\\max\\{\\log N,t'\\}$ is compatible with HR checks

- `Lens:` Equivalence.
- `Statement (Q43.S134-s1-swap-compatibility):`
  In HR parameterization (Proof of Thm. 4.3), you can replace the starting value
  $$s_1:=\\log N\\quad\\text{on}\\quad s_1:=\\max\\{\\log N,t'\\}$$
  without changing the correctness of checks Lemma 4.4/4.5: all inequalities in $s_\\eta$
  and $t(\\eta)$ are preserved for sufficiently large $n$ in the mode $M=\\mathrm{poly}(n)$,
  $s=\\mathrm{polylog}(n)$.
- `Rationale:`
  1) According to Section 16.166, all HR parameters depend on $s_\\eta$ only through definitions
     $s_\\eta=2^{\\eta-1}s_1$ and $t(\\eta)=\\sum_{i\\le\\eta}s_i+\\log M$, and the conditions Lemma 4.4
     require $t'\\le s_\\eta\\le n'/32$.
  2) Replacing $s_1\\rightsquigarrow\\max\\{\\log N,t'\\}$ makes $s_\\eta$ and $t(\\eta)$ **monotonically**
     more, so $t'\\le s_\\eta$ is automatically performed, and the rest of the checks
     are reduced to control $t(\\eta)\\le n_\\eta/16$.
  3) In the mode Section 16.276 we have $t'=(2s+1)\\log M=\\log^{O(1)}n$ and
     $n_\\eta\\ge n/\\mathrm{polylog}(n)^\\eta$ for $\\eta\\le d=O(\\log n/\\log\\log n)$,
     this means $t(\\eta)=\\mathrm{polylog}(n)\\ll n_\\eta$ for a sufficiently large $n$.
  Consequently, replacing $s_1$ does not violate the HR check and only strengthens the local depth $s_\\eta$.
- `Toy test:` let $n=2^{40}$, $N=n^2$, $M=n^2$, $s=\\log n$; then $t'\\approx(2s+1)\\log M\\approx 6400$,
  $s_1=\\max\\{\\log N,t'\\}=\\max\\{80.6400\\}=6400$, and $s_\\eta=2^{\\eta-1}s_1$ remains
  $\\ll n'/32$ for $n'\\ge n^{0.9}$, and $t(\\eta)=O(2^\\eta s_1)$ is still $\\ll n_\\eta$.
- `Status:` reduction/equivalence (correctness of replacement $s_1$).
- `StepID:` Q43.S134-s1-swap-compatibility.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (monotonic parameter estimates, the oracle is not involved).
  B) Natural proofs check: not applicable (no property of functions/lower bounds for circuits).
  C) Algebrization check: not applicable (no arithmetization/extension oracle).
- `Next step:` localize the exact location in HR Lemma 4.5 where $s_1=\\log N$
  used as **equality** rather than as a lower bound, or to confirm the absence
  such a place (Q43.S135-s1-use-audit).

### 16.278. Research step (exact citation): where exactly is $s_1=\\log N$ used in Proof of Thm. 4.3

- `Lens:` Invariant.
- `Statement (Q43.S135-s1-use-audit):`
  In Proof of Thm. 4.3 (HR'22) parameter $s_1=\\log N$ is included **only** through the definition
  $s_\\eta=2^{\\eta-1}\\log N$ and the subsequent $t(\\eta)=\\sum_{i\\le\\eta}s_i+\\log M$,
  and in the formulation of Lemma 4.5 only the sums $\\sum_{i\\le\\eta}s_i$ and the condition are used
  $t(\\eta)\\le n_\\eta/16$. Therefore, the replacement $s_1\\to\\max\\{\\log N,t'\\}$ affects only
  values $s_\\eta$ and $t(\\eta)$, without other hidden dependencies on $\\log N$.
- `Exact citation:`
  In Proof of Thm. 4.3 parameters are fixed as
  “The parameter s depends on η and is fixed to s = sη = 2η−1 log N. With these parameters in place we can
  finally also fix t() = i<= si + log M ..." and further Lemma 4.5 uses depth
  $\\sum_{i<\\eta}s_i$ and condition $t(\\eta)\\le n_\\eta/16$
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1099–1109`).
- `Toy test:` when replacing $\\log N$ with $\\max\\{\\log N,t'\\}$ all mentions of $s_\\eta$ and $t(\\eta)$
  grow monotonically, and there are no other direct appearances of $\\log N$ in Lemma 4.5.
- `Status:` exact citation (audit of usage $s_1=\\log N$).
- `StepID:` Q43.S135-s1-use-audit.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (checking against the text, the oracle is not involved).
  B) Natural proofs check: not applicable (no property of functions/lower bounds for circuits).
  C) Algebrization check: not applicable (no arithmetization/extension oracle).
- `Next step:` scan the remaining Proof of Thm spaces. 4.3 and Lemma 4.5 on
  direct occurrences of $\\log N$ outside $s_\\eta$/$t(\\eta)$ (Q43.S136-logn-occurrence-scan).

### 16.279. Research step (exact citation): scan $\\log N$ in Proof of Thm. 4.3/Lemma 4.5

- `Lens:` Equivalence.
- `Statement (Q43.S136-logn-occurrence-scan):`
  In Proof of Thm. 4.3 and Lemma 4.5 direct occurrences of $\\log N$ occur only
  in the definition of $s_\\eta=2^{\\eta-1}\\log N$ and in the estimates for $t(\\eta)$/ $t(d)$; others
  there are no references to $\\log N$ in these places.
- `Exact citation:`
  In Proof of Thm. 4.3 $s_\\eta=2^{\\eta-1}\\log N$ is fixed and
  $t(\\eta)=\\sum_{i\\le\\eta}s_i+\\log M\\le 2^\\eta\\log N+\\log M$,
  and Lemma 4.5 uses the depth $\\sum_{i<\\eta}s_i$ and the condition
  $t(\\eta)\\le n_\\eta/16$ (HR’22, `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1099–1109`).
  At the end of Proof of Thm. 4.3 $t(d)\\le 2^d\\log N+\\log M$ is used again
  (`…:1232`).
- `Toy test:` `rg -n "log N" ...` in the specified fragments gives only these appearances;
  other occurrences (for example `…:980`) refer to earlier evidence and are not
  participate in Proof of Thm. 4.3/Lemma 4.5.
- `Status:` exact citation (audit of direct occurrences of $\\log N$).
- `StepID:` Q43.S136-logn-occurrence-scan.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (text check).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` scan remaining places in Section 4 (outside Proof of Thm. 4.3/Lemma 4.5)
  on direct occurrences of $\\log N$ and clarify whether they belong to Q43 (Q43.S137-logn-remaining-scan).

### 16.280. Research step (exact citation): the remaining $\\log N$ in Section 4 is the Proof of Thm. 4.1

- `Lens:` Invariant.
- `Statement (Q43.S137-logn-remaining-scan):`
  Remaining direct occurrences of $\\log N$ in Section 4 (outside Proof of Thm. 4.3/Lemma 4.5)
  refer to Proof of Thm. 4.1 (singleswitching): $s=152\\log N$ is fixed there,
  and also uses $t_d=152\\log N$ and the inequality $\\log N\\le n^{1/d}/(c_1\\log^4 n)$.
  These places are not included in the Q43 port of Lemma 4.5.
- `Exact citation:`
  Proof of Thm. 4.1: “set $s=152\\log N$ … let $t_i=s$ … $t_d=152\\log N$ … if $\\log N\\le n^{1/d}/(c_1\\log^4 n)$”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:980–1028`).
- `Toy test:` search `log N` outside Proof of Thm. 4.3/Lemma 4.5 gives only block 980-1028,
  and it ends with the phrase "The claimed lower bound follows. We turn our attention to the main result"
  before Theorem 4.3.
- `Status:` exact citation (residual occurrences of $\\log N$ are localized in Thm. 4.1).
- `StepID:` Q43.S137-logn-remaining-scan.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (text check).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check if Proof of Thm is used. 4.1 as a sub-step in Proof of Thm. 4.3
  (or fix that they are independent) - Q43.S138-logn-nonimpact-check.

### 16.281. Exploratory step (toy): poly$M$ vs threshold $2^{n^{\\alpha}}$ in Thm. 4.3

- `Lens:` Trade-off.
- `Approval (verification):` compare polynomial$M$ with threshold
  $2^{n^{\\alpha}}$, where $\\alpha=1/d-1/(d(d-1))$ and $d=\\lfloor\\log_2 n/\\log_2\\log_2 n\\rfloor$.
  Here the base is consistent with $\\log_2$ (HR convention); going to $e^x$ gives only the factor $\\ln 2$ in the exponent.
- `Toy test:` script `scripts/toy_q43_s141.py` for $n=2^8,\\dots,2^{32}$ and $k\\in\\{1,2,4,8\\}$
  shows that $n^{\\alpha}\\lesssim\\log n$, so already for $k=1$ we have $k\\log n>n^{\\alpha}$
  (and even more so for $k\\ge 2$). This means $M=n^k$ is **not** less than $2^{n^{\\alpha}}$.
  Example: $n=2^{16}$, $d=4$, $\\alpha=1/6$, $n^{\\alpha}\\approx 6.35$, and $k\\log n\\approx 22.2$ for $k=2$.
- `Status:` toy-computation (threshold large-$M$ is not automatically higher than polynomial-$M$ at $d=\\Theta(\\log n/\\log\\log n)$).
- `StepID:` Q43.S141-poly-vs-exp-threshold.
- `InfoGain:` 1.
- `Next step:` clarify HR parameterization (what exactly does $n$ mean in the threshold)
  and compare with the actual polynomial regime $M=\\mathrm{poly}(N)$.

### 16.282. Research step (exact citation): Thm parameters. 4.3 - $n$ is the side of the grid, $N$ is the length of the proof

- `Lens:` Trade-off.
- `Statement (Q43.S142-parameter-map-n-vs-bign):`
  In the formulation of HR'22 Theorem 4.3, $n$ is the side of the $n\\times n$ grid in Tseitin($G_n$),
  $N$ is the number of lines (length) of the Frege proof, and each line has size $M$ and depth $d$.
  The lower bound is expressed as
  $$N\\ \\ge\\ 2^{\\Omega\\left(\\frac{n}{((\\log n)^{O(1)}\\,\\log M)^d}\\right)},$$
  where $\\log$ is based on $2$ (HR convention).
  In Proof of Thm. 4.3 the parameter large$M$ is formulated as $M\\le 2^{n^{1/d-1/(d(d-1))}}$,
  where $n$ is the same size of the grid side.
- `Exact citation:`
  Thm formulation. 4.3: "Tseitin($G_n$) with odd charges at all nodes of the $n\\times n$ grid ... If each line
  of the refutation is of size $M$ and depth $d$, then the number of lines in the refutation is
  $\\exp\\,\\Omega\\bigl(n/((\\log n)^{O(1)}\\log M)^d\\bigr)$" and further "Suppose we are given a Frege refutation ...
  consisting of $N$ lines” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:939–962`).
  In Proof of Thm. 4.3: "Suppose we are given a proof of length $N=\\exp(n/((\\log n)^c\\log M)^d)$ ...
  We may assume that $M\\le\\exp(n^{1/d-1/d(d-1)})$” (`…:1104–1106`; `exp` in the quote = $2^x$ according to the $\\log_2$ convention in HR'22).
- `Status:` exact citation (fixing parameters $n,N,M,d$ and exponent base).
- `StepID:` Q43.S142-parameter-map-n-vs-bign.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (text check).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` express $n$ in terms of formula size/number of variables
  (for example, $|\\mathrm{Tseitin}(G_n)|=\\Theta(n^2)$) and rewrite the threshold large$M$
  in terms of $N$ or $|F|$ for comparison with the poly$M$ mode.

### 16.283. Exploratory step (reduction): converting parameter $n$ into formula size for Tseitin(Grid)

- `Lens:` Equivalence.
- `Statement (Q43.S143-translate-n-parameter):`
  Let $G_n$ be $n\\times n$ grid. Then $|V|=n^2$ and $|E|=2n(n-1)$.
  In Tseitin($G_n$) each variable corresponds to an edge, so the number of variables
  $$N_{\\mathrm{var}}:=|E|=2n(n-1)=\\Theta(n^2).$$
  For a standard CNF parity encoding at a vertex of degree $d$, $2^{d-1}$ clauses are needed,
  therefore, for grid (degrees $2,3,4$) the number of clauses is equal to
  $$2\\cdot 4\\ +\\ 4\\cdot 4(n-2)\\ +\\ 8\\cdot (n-2)^2\\ =\\ 8(n-1)^2\\ =\\ \\Theta(n^2).$$
  Therefore, $|F_n|=\\Theta(n^2)$ and
  $$n=\\Theta(\\sqrt{N_{\\mathrm{var}}})=\\Theta(\\sqrt{|F_n|}).$$
  Therefore, large$M$ is the threshold from HR Thm. 4.3
  $$M\\le 2^{n^{\\alpha}},\\qquad \\alpha=1/d-1/(d(d-1)),$$
  rewritten as
  $$M\\le 2^{(N_{\\mathrm{var}})^{\\alpha/2}}=2^{|F_n|^{\\alpha/2}},$$
  where the base is consistent with $\\log_2$ (HR convention).
- `Toy test:` $n=4$ gives $|E|=2\\cdot 4\\cdot 3=24$ and $8(n-1)^2=72$ clauses,
  which is consistent with $\\Theta(n^2)$.
- `Status:` reduction/equivalence (relationship of parameter $n$ with $N_{\\mathrm{var}}$ and $|F_n|$).
- `StepID:` Q43.S143-translate-n-parameter.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (combinatorial recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` substitute $n=\\Theta(\\sqrt{|F|})$ into the threshold large$M$
  and compare with the regime $M=\\mathrm{poly}(|F|)$ with $d=\\Theta(\\log n/\\log\\log n)$.

### 16.284. Exploratory step (reduction): large$M$ threshold vs $M=\\mathrm{poly}(|F|)$ at $d=\\kappa\\,\\log n/\\log\\log n$

- `Lens:` Trade-off.
- `Statement (Q43.S144-translate-largem-vs-polyn):`
  Let $d=\\kappa\\,\\frac{\\log n}{\\log\\log n}$ (constant $\\kappa>0$),
  and large$M$ threshold from HR Thm. 4.3 is written as
  $$M\\le 2^{n^{\\alpha}},\\qquad \\alpha=\\frac1d-\\frac1{d(d-1)}.$$
  Then for $n=\\Theta(\\sqrt{|F|})$ we obtain
  $$n^{\\alpha}=2^{(1+o(1))\\frac{\\log n}{d}}
      =2^{(1+o(1))\\frac{\\log\\log n}{\\kappa}}
      =(\\log n)^{1/\\kappa+o(1)},$$
  and, since $\\log n=\\tfrac12\\log|F|+O(1)$,
  $$2^{n^{\\alpha}}=2^{\\Theta\\bigl((\\log|F|)^{1/\\kappa}\\bigr)}.$$
  For $M=|F|^k=2^{k\\log|F|}$ the comparison depends on $\\kappa$:
  1) $\\kappa<1$: $1/\\kappa>1$, so $2^{(\\log|F|)^{1/\\kappa}}$ **superpolynomial**
     (since $2^{(\\log n)^p}$ is superpolynomial for $p>1$), and poly$M$ remains below the threshold.
  2) $\\kappa=1$: threshold $2^{\\Theta(\\log|F|)}=|F|^{\\Theta(1)}$; at exact coefficient
     from $n=\\Theta(\\sqrt{|F|})$ we obtain the threshold $|F|^{1/2+o(1)}$, so poly$M$ with $k>1/2$
     **exceeds** threshold.
  3) $\\kappa>1$: $2^{(\\log|F|)^{1/\\kappa}}=|F|^{o(1)}$ (subpolynomial), therefore
     any $M=|F|^k$ with $k>0$ **exceeds** the threshold.
- `Toy test:` for $\\kappa=1$ and $|F|=n^2$ we have the threshold $M\\lesssim n=|F|^{1/2}$,
  then $M=|F|$ already falls into the large$M$ branch.
- `Status:` reduction (comparing large$M$ threshold with polynomial$M$ in terms of $|F|$).
- `StepID:` Q43.S144-translate-largem-vs-polyn.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` fix a specific $\\kappa$ value from the one being used
  depth mode and conclude whether the Theorem 4.1 branch is applicable for $M=\\mathrm{poly}(|F|)$.

### 16.285. Exploratory step (reduction): mode selection $\\kappa$  large$M$ branch for poly$M$

- `Lens:` Invariant.
- `Statement (Q43.S145-kappa-regime-decision):`
  In the target depth mode $d=\\kappa\\,\\log n/\\log\\log n$ we fix $\\kappa\\ge 1$
  (for example, $\\kappa=59$ from the Hastad'20 range for gridLB), then
  $$2^{n^{\\alpha}}=2^{\\Theta\\bigl((\\log|F|)^{1/\\kappa}\\bigr)}
     =|F|^{o(1)}\\quad\\text{for }\\kappa>1,$$
  and for $\\kappa=1$ the threshold has the form $|F|^{1/2+o(1)}$.
  Consequently, for any $M=|F|^k$ with $k>0$ we find ourselves in the large$M$ branch
  (for $\\kappa>1$ always, for $\\kappa=1$ - when $k>1/2$).
  For comparison: for $\\kappa<1$ we get $2^{(\\log|F|)^{1/\\kappa}}$ with $1/\\kappa>1$,
  which means the threshold is superpolynomial (see rule: $2^{(\\log n)^p}$ is superpolynomial for $p>1$).
- `Toy test:` for $\\kappa=1$, $|F|=n^2$, threshold $M\\lesssim n=|F|^{1/2}$, so $M=|F|$
  already falls into the large-$M$ branch.
- `Status:` reduction (the $\\kappa\\ge 1$ mode and the corresponding large$M$ branch are fixed).
- `StepID:` Q43.S145-kappa-regime-decision.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` confirm the selected $\\kappa$ value from a specific source
  (for example, deep mode/constants in the used LB/UB) and fix the output
  on the applicability of the Theorem 4.1 branch for $M=\\mathrm{poly}(|F|)$.

### 16.286. Research step (exact citation): constant $\\kappa=59$ from Hastad'20 Thm. 6.5

- `Lens:` Invariant.
- `Statement (Q43.S146-kappa-constant-source):`
  In Hastad (2020), Theorem 6.5, the depth is limited as
  $$d\\le 59\\,\\frac{\\log n}{\\log\\log n},$$
  where $n$ is the side of the $n\\times n$ grid. This fixes the $\\kappa=59$ mode for
  scale $d=\\kappa\\log n/\\log\\log n$.
  In the text nearby there is a dimensional lower bound of the form $2^{(\\cdot)}$; here is the base
  does not affect the extraction of $\\kappa$, but in our notes we use $2^x$
  (with transition to $e^x$ through the factor $\\ln 2$ in the exponent).
- `Exact citation:`
  In the PDF text layer, the fraction is typed "in a column": line with the numerator `log n`
  just before Theorem 6.5 and Theorem 6.5 line from `d ≤ 59 log log n`
  ("log n" over "log log n"), which gives $d\\le 59\\,\\log n/\\log\\log n$
  (`resources/text_cache/hastad_2020_small_depth_frege_tseitin_grids.txt:825–826`).
- `Status:` exact citation (constant $\\kappa=59$ in depth mode).
- `StepID:` Q43.S146-kappa-constant-source.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (quote in the text).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` apply $\\kappa=59$ in the output of Section 16.284-Section 16.285 and
  fix that poly$M$ falls into the large$M$ branch of Theorem 4.1.

-/

/-!
### 16.287. Exploratory step (reduction): $\\kappa=59$ commits a large$M$ branch for poly$M$

- `Lens:` Trade-off.
- `Statement (Q43.S147-apply-thm41-branch):`
  From Section 16.285 and $\\kappa=59>1$ (Hastad'20, Thm. 6.5) we obtain that large$M$ threshold
  $$M\\le 2^{\\Theta\\bigl((\\log|F|)^{1/\\kappa}\\bigr)}
     =2^{\\Theta\\bigl((\\log|F|)^{1/59}\\bigr)}$$
  is $|F|^{o(1)}$ (subpolynomial).
  Therefore, any $M=|F|^k$ with $k>0$ eventually **exceeds** the threshold, and in Thm. 4.3
  for poly$M$ the large$M$ branch is always chosen, that is, the transition to Thm. 4.1;
  the small-$M$ branch is relevant only when $M$ is below the threshold (subpolynomial for $\\kappa>1$).
  (For $\\kappa<1$ the threshold would be superpolynomial, since
  $2^{(\\log n)^p}$ is superpolynomial for $p>1$.)
- `Status:` reduction (the large$M$ branch is fixed at $\\kappa=59$).
- `StepID:` Q43.S147-apply-thm41-branch.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check where exactly in Proof of Thm. 4.3 uses the Thm branch. 4.1,
  and make sure that poly$M$ does not require it.

-/

/-!
### 16.288. Research step (exact citation): Proof of Thm. 4.3 - Thm. 4.1 applies when $M$ is above the threshold

- `Lens:` Invariant.
- `Statement (Q43.S148-thm41-branch-audit):`
  In Proof of Theorem 4.3, the authors explicitly separate the $M\\le 2^{n^{\\alpha}}$ branch and write,
  that for $M$ **above** the threshold, Theorem 4.1 can be applied. Reminder:
  $2^{(\\log n)^p}$ is superpolynomial for $p>1$, but here $p<1$ in the mode
  $d=\\kappa\\log n/\\log\\log n$.
- `Exact citation:`
  Proof of Theorem 4.3: “We may assume that $M\\le \\exp(n^{1/d-1/d(d-1)})$, as otherwise we can
  apply Theorem 4.1.” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1104–1106`; `exp` in the quote = $2^x$ according to the $\\log_2$ convention in HR'22).
- `Status:` exact citation (thread Thm. 4.1 = case $M$ above threshold).
- `StepID:` Q43.S148-thm41-branch-audit.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (quote in the text).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` write out the explicit lower bound from Thm. 4.1 in $M=\\mathrm{poly}(|F|)$ mode
  and compare with parameters $|F|,N$.

-/

/-!
### 16.289. Research step (reduction): large$M$ Thm branch. 4.1 in mode $d=\\kappa\\log n/\\log\\log n$

- `Lens:` Equivalence.
- `Statement (Q43.S149-largem-bound-from-thm41):`
  Thm. 4.1 gives a lower estimate
  $$N\\ \\ge\\ 2^{\\Omega\\bigl(n^{1/d}/\\log^4 n\\bigr)},$$
  where the base is consistent with $\\log_2$ (HR convention).
  In the mode $d=\\kappa\\,\\log n/\\log\\log n$ we have
  $$n^{1/d}=2^{\\tfrac{\\log n}{d}}
            =2^{\\tfrac{\\log\\log n}{\\kappa}}
            =(\\log n)^{1/\\kappa+o(1)},$$
  and therefore
  $$N\\ \\ge\\ 2^{\\Omega\\bigl((\\log n)^{1/\\kappa-4+o(1)}\\bigr)}.$$
  For $|F|=\\Theta(n^2)$ we get
  $$N\\ \\ge\\ 2^{\\Omega\\bigl((\\log|F|)^{1/\\kappa-4+o(1)}\\bigr)}.$$
  When $\\kappa=59$ the exponent is negative, which means bound is subpolynomial:
  $$N\\ \\ge\\ 2^{\\Omega((\\log|F|)^{-3.98\\ldots})}=|F|^{o(1)}.$$
  Reminder: $2^{(\\log n)^p}$ is superpolynomial for $p>1$,
  but here $p=1/\\kappa-4<1$.
- `Exact citation:`
  Thm. 4.1: “For $d=O(\\log n/\\log\\log n)$ … requires size $\\exp\\,\\Omega(n^{1/d}/\\log^4 n)$”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:846–850`).
- `Status:` reduction (translation of bound Thm. 4.1 into parameters $|F|$ and $\\kappa$).
- `StepID:` Q43.S149-largem-bound-from-thm41.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` compare this bound with the parameters $N,|F|,M$ in the target model
  and check if there is a mode where Thm. 4.1 gives non-trivial superpolynomiality.

-/

/-!
### 16.290. Research step (reduction): Thm. 4.1 vs polymode $N,|F|,M$ at $\\kappa=59$

- `Lens:` Trade-off.
- `Statement (Q43.S150-thm41-bound-compare):`
  In target mode $M=|F|^k$ and $N=|F|^C$ (polynomial lines and proof length)
  large$M$ thread Thm. 4.1 gives
  $$N\\ \\ge\\ 2^{\\Omega\\bigl((\\log|F|)^{1/\\kappa-4+o(1)}\\bigr)}.$$
  At $\\kappa=59$ the indicator is $1/\\kappa-4<0$, so
  $$N\\ \\ge\\ 2^{\\Omega((\\log|F|)^{-3.98\\ldots})}=|F|^{o(1)},$$
  that is, bound is **subpolynomial** and is automatically satisfied for any $N=|F|^C$.
  Moreover, to obtain a superpolynomial lower bound of the form
  $2^{(\\log|F|)^p}$ with $p>1$, you need $1/\\kappa-4>1$, that is, $\\kappa<1/5$.
  Reminder: $2^{(\\log n)^p}$ is superpolynomial for $p>1$.
- `Exact citation:`
  Thm. 4.1 is formulated as $\\exp\\,\\Omega(n^{1/d}/\\log^4 n)$ (see.
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:846–850`).
- `Status:` reduction (comparing bound Thm. 4.1 with polymode).
- `StepID:` Q43.S150-thm41-bound-compare.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check if there is a realistic depth mode
  $d=\\kappa\\log n/\\log\\log n$ with $\\kappa<1/5$ (or other scale $d$),
  where Thm. 4.1 gives superpolynomiality for grid-Tseitin.

-/

/-!
### 16.291. Research step (barrier certificate): hidden constants in Lemma 4.2 prevent the $\\kappa<1/5$ mode from being fixed

- `Lens:` Invariant.
- `Statement (Q43.S151-thm41-nontrivial-regime):`
  To obtain superpolynomiality from Thm. 4.1 mode
  $d=\\kappa\\log n/\\log\\log n$, you need $\\kappa<1/5$ (see Section 16.290),
  that is, explicit constants are required in the condition $d=O(\\log n/\\log\\log n)$.
  However Thm. 4.1 is formulated with bigO without an explicit coefficient,
  and the key Lemma 4.2 speaks only about the existence of absolute constants $A,C,n_0$.
  Therefore, it cannot be strictly stated that a particular regime $\\kappa<1/5$ falls within
  to the domain of applicability of the theorem. This is a local barrier to withdrawal
  superpolynomiality for poly$M$ ($2^{(\\log n)^p}$ is superpolynomial for $p>1$).
- `Exact citation:`
  Thm. 4.1: “For $d=O(\\log n/\\log\\log n)$ … requires size $\\exp\\,\\Omega(n^{1/d}/\\log^4 n)$”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:846–850`).
  Lemma 4.2: “There are absolute constants $A,C,n_0>0$ …” (`...:858–859`).
- `Status:` barrier certificate (implicit constants block mode checking $\\kappa<1/5$).
- `StepID:` Q43.S151-thm41-nontrivial-regime.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract explicit constants from the proof of Lemma 4.2/Thm. 4.1
  or go to the explicit constant from Hastad'20 Thm. 6.5 for comparison.

-/

/-!
### 16.292. Exploratory step (exact citation): explicit parameters in Proof of Thm. 4.1 (step to extract constants)

- `Lens:` Equivalence.
- `Statement (Q43.S152-extract-constants):`
  In Proof of Thm. 4.1 the explicit induction parameters are fixed:
  $$s=152\\log N,\\quad t_i=s,\\quad n_i=\\bigl\\lfloor n_{i-1}/(4A t_{i-1}\\log^4 n_{i-1})\\bigr\\rfloor,$$
  and also the condition
  $$\\log N\\le n^{1/d}/(c_1\\log^4 n),$$
  where $A$ is the constant from Lemma 4.2 and $c_1$ is a sufficient absolute constant.
  These are the only explicit numerical constants in the proof that can be
  used for subsequent extraction of the acceptable coefficient in
  $d=O(\\log n/\\log\\log n)$. (For context: $\\exp=e^x$ in HR notation; change of base
  does not affect the valid $\\kappa$ check here.)
- `Exact citation:`
  “We choose $t_0=1$ and $n_0=n$, set $s=152\\log N$, and let $t_i=s$ and
  $n_i=\\lfloor n_{i-1}/(4A t_{i-1}\\log^4 n_{i-1})\\rfloor$ …”  
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:889–891`).
  “Thus if $\\log N\\le n^{1/d}/(c_1\\log^4 n)$ for constant $c_1>0$ large enough, then we
  get a contradiction …” (`...:930–931`).
- `Status:` exact citation (explicit parameters of Proof of Thm. 4.1 are fixed).
- `StepID:` Q43.S152-extract-constants.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (quote in the text).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` based on these parameters, try to derive an explicit coefficient
  in deep mode $d=\\kappa\\log n/\\log\\log n$ (or show that this is impossible without
  extracting $A$ from Lemma 4.2).

-/

/-!
### 16.293. Research step (barrier certificate): implicit $A_0,A_1,A_2$ in Proof of Lemma 4.2 blocks explicit $\\kappa$

- `Lens:` Invariant.
- `Statement (Q43.S153-kappa-constant-derivation):`
  An attempt to derive an explicit $\\kappa$ coefficient for the mode
  $d=\\kappa\\log n/\\log\\log n$ rests on the implicit constants in Proof of Lemma 4.2.
  There the probability is limited by "absolute constant $A$" (from Lemma 6.9) and
  "appropriate constants $A_0,A_1,A_2$", without numeric values. These constants are included
  into exponential factors of the form $A_1^s, A_2^s$ and therefore directly affect
  admissible coefficient in $O(\\log n/\\log\\log n)$. Therefore, without explicit
  extracts $A_0,A_1,A_2$ cannot strictly confirm the mode $\\kappa<1/5$
  (even with $\\exp=e^x$; replacing with $2^x$ only reduces the thresholds).
- `Exact citation:`
  Proof of Lemma 4.2: “for some absolute constant $A$ …” and “for appropriate constants
  $A_0,A_1,A_2$” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1972–1974, 1996`).
- `Status:` barrier certificate (implicit constants block explicit $\\kappa$).
- `StepID:` Q43.S153-kappa-constant-derivation.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` try to calculate the numerical values of $A_0,A_1,A_2$
  from Proof of Lemma 6.9/6.8 or fix the impossibility without recalculating the entire estimate.

-/

/-!
### 16.294. Exploratory step (exact citation): explicit constants from Lemma 6.8/6.9

- `Lens:` Equivalence.
- `Statement (Q43.S154-lemma42-constants-extract):`
  Within the Lemma 6.8/6.9 chain, the explicit numerical constant is
  only estimate $s/64\\le a$ (and $b\\le 3a$), whereas Lemma 6.9 introduces
  only the existence of an absolute constant $A>0$ in the upper bound
  number of additional bits. This means that from the text directly
  only the coefficient $1/64$ is extracted, and the numerical value $A$ is not specified.
- `Exact citation:`
  Lemma 6.8: “It holds that $b \\le 3a$, and $s/64 \\le a$.”  
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1944`).
  Lemma 6.9: “There is a constant $A>0$ such that the following holds …”
  (`...:1960`).
- `Status:` exact citation (explicit constants: $1/64$ only, $A$ not specified).
- `StepID:` Q43.S154-lemma42-constants-extract.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (quote in the text).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` try to estimate $A$ from Proof of Lemma 6.9 (bit counting)
  or record that this requires a complete recalculation of the design.

-/

/-!
### 16.295. Research step (barrier certificate): There is no explicit number for $A$ in Proof of Lemma 6.9

- `Lens:` Invariant.
- `Statement (Q43.S155-lemma69-constant-extract):`
  Proof of Lemma 6.9 operates on "constant number/amount of bits per potential edge" and
  completes the calculation with the formula "another $A|S^*_g|$ bits for some constant $A$", but nowhere
  does not give a numerical value for $A$. Therefore, retrieving explicit $A$ requires
  complete recalculation of the design (and all hidden "constant number of bits"),
  which is beyond the scope of the current step.
- `Exact citation:`
  “read … a constant number of bits per potential edge” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2066–2069`),
  “read a constant amount of extra information per potential edge” (`...:2108–2110`),
  “we need another $A|S^*_g|$ bits for some constant $A$” (`...:2111–2114`).
- `Status:` barrier certificate (explicit $A$ is not extracted without a full recalculation).
- `StepID:` Q43.S155-lemma69-constant-extract.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` fix this barrier as permanent or carry out
  separate complete recalculation of Proof of Lemma 6.9 with explicit constants.

-/

/-!
### 16.296. Research step (barrier certificate): full recalculation of Lemma 6.9 required for explicit $A$

- `Lens:` Invariant.
- `Statement (Q43.S156-lemma69-recount-needed):`
  In Lemma 6.9 and its proof-outline, the cost is estimated using "constant number/amount of bits"
  and the multiplier $A|S^*_g|$, while none of these constants are parameterized.
  This means that the explicit numeric value of $A$ can only be obtained through
  complete recalculation of the entire structure (including all "constant" bit estimates),
  which is significantly beyond the scope of the current step. We record this as
  constant local barrier to extracting explicit $\\kappa$ from Thm. 4.1.
- `Exact citation:`
  “constant number of bits per potential edge” and “another $A|S^*_g|$ bits for some constant $A$”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2066–2069, 2111–2114`).
- `Status:` barrier certificate (explicit $A$ is not extracted without a full recalculation).
- `StepID:` Q43.S156-lemma69-recount-needed.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or accept the barrier and switch to explicit constants
  from Hastad'20 (Thm. 6.5), or plan a separate complete recalculation of Lemma 6.9.

-/

/-!
### 16.297. Research step (exact citation): pivot to Hastad'20 Thm. 6.5 with explicit $\\kappa$ and base $2^x$

- `Lens:` Trade-off.
- `Statement (Q43.S157-pivot-hastad20-kappa):`
  In Hastad (2020), Thm. 6.5, depth limited as
  $$d\\le 59\\,\\frac{\\log n}{\\log\\log n},$$
  where $n$ is the side of the $n\\times n$ grid, and at the same time it is asserted
  $$\\mathrm{size}\\ge 2^{\\Omega(n^{1/(58(d+1))})}.$$
  The base does not affect the extraction of $\\kappa$, but it does affect the thresholds:
  $2^{(\\log n)^p}$ is superpolynomial for $p>1$.
  This fixes the explicit constant $\\kappa=59$ for the mode $d=\\kappa\\log n/\\log\\log n$,
  which allows you to move from implicit HR'22 constants to an explicit depth threshold.
- `Exact citation:`
  numerator string `log n` just before Theorem 6.5 and the lines
  `Theorem 6.5. Suppose that d ≤ 59 log log n` and
  `requires size exp(Ω(n 1/58(d +1) ))`
  (`resources/text_cache/hastad_2020_small_depth_frege_tseitin_grids.txt:825–827`; `exp` in the quote = $2^x$, logarithms - based on base 2).
- `Status:` exact citation (explicit $\\kappa=59$ and expLB form).
- `StepID:` Q43.S157-pivot-hastad20-kappa.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (quote in the text).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` apply $\\kappa=59$ to the large$M$ threshold in Thm. 4.3
  and check the mode for $M=\\mathrm{poly}(|F|)$.

-/

/-!
### 16.298. Research step (reduction): at $\\kappa=59$ the threshold large-$M$ is subpolynomial, which means $M=\\mathrm{poly}(|F|)$ is always in the large-branch

- `Lens:` Equivalence.
- `Statement (Q43.S158-largem-branch-polym-check):`
  Let $d=\\kappa\\log n/\\log\\log n$ with $\\kappa=59$ (Hastad'20, Thm. 6.5) and $|F|=\\Theta(n^2)$ for Tseitin(Grid$_n$).
  Then the threshold is large$M$ in Thm. 4.3 looks like
  $$M\\le 2^{\\Theta\\bigl((\\log|F|)^{1/\\kappa}\\bigr)}
      =2^{\\Theta\\bigl((\\log|F|)^{1/59}\\bigr)},$$
  Since $(\\log|F|)^{1/59}=o(\\log|F|)$, we have
  $$2^{\\Theta((\\log|F|)^{1/59})}=|F|^{o(1)},$$
  that is, the threshold is subpolynomial. Therefore, for any $k>0$ and sufficiently large $|F|$
  $|F|^k$ is executed above the threshold, and the large$M$ branch (that is, the transition to Thm. 4.1)
  applies to all $M=\\mathrm{poly}(|F|)$.
  Reminder: $2^{(\\log n)^p}$ is superpolynomial for $p>1$, but here $p=1/59<1$.
- `Toy test:` $|F|=n^2$: threshold $2^{(2\\log n)^{1/59}}=n^{o(1)}$, so $M=|F|$ is already in the large branch.
- `Status:` reduction (large$M$ branch is fixed for $M=\\mathrm{poly}(|F|)$ at $\\kappa=59$).
- `StepID:` Q43.S158-largem-branch-polym-check.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` link large branch Thm. 4.3 with explicit evaluation from Thm. 4.1
  in terms of $|F|$ and $M=\\mathrm{poly}(|F|)$.

-/

/-!
### 16.299. Research step (reduction): translation of Thm assessment. 4.1 in terms of $|F|$ for poly$M$

- `Lens:` Trade-off.
- `Statement (Q43.S159-thm41-bound-translate):`
  In the large-$M$ branch (for $M=\\mathrm{poly}(|F|)$) Thm is applicable. 4.1:
  $$N\\ \\ge\\ 2^{\\Omega\\bigl(n^{1/d}/\\log^4 n\\bigr)}.$$
  For grid-Tseitin $|F|=\\Theta(n^2)$, so $\\log n=\\tfrac12\\log|F|+O(1)$ and
  $$n^{1/d}=2^{\\tfrac{\\log n}{d}}
            =2^{\\tfrac{\\log\\log n}{\\kappa}}
            =(\\log n)^{1/\\kappa+o(1)}.$$
  For $d=\\kappa\\log n/\\log\\log n$ with $\\kappa=59$ we obtain
  $$N\\ \\ge\\ 2^{\\Omega\\bigl((\\log|F|)^{1/\\kappa-4+o(1)}\\bigr)}
      =2^{\\Omega((\\log|F|)^{-3.98\\ldots})}=|F|^{o(1)}.$$
  This means that for any $N=|F|^C$ bound is executed automatically and does not prohibit polysize.
  Reminder: $2^{(\\log n)^p}$ is superpolynomial for $p>1$, but here $p<1$.
- `Exact citation:`
  Thm. 4.1: “For $d=O(\\log n/\\log\\log n)$ … requires size $\\exp\\,\\Omega(n^{1/d}/\\log^4 n)$”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:846–850`).
- `Toy test:` $|F|=n^2$ gives a threshold of $2^{(\\log n)^{1/59}/\\log^4 n}=n^{o(1)}$, so $N=|F|$
  already above lower bound.
- `Status:` reduction (translation of bound Thm. 4.1 into $|F|$ for poly$M$).
- `StepID:` Q43.S159-thm41-bound-translate.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (asymptotic recalculation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` try to extract explicit constants from Lemma 4.2/Proof of Thm. 4.1
  or fix the impossibility without a complete recount.

-/

/-!
### 16.300. Research step (barrier certificate): in Proof Thm. 4.1 constants $c_1,c_2$ are specified only as "large/some"

- `Lens:` Invariant.
- `Statement (Q43.S160-thm41-const-extract):`
  In Proof of Thm. 4.1 (HR'22) the conditions for size are formulated through
  $$N\\le \\exp\\bigl(n^{1/d}/(c_1\\log^4 n)\\bigr)$$
  for "large constant $c_1>0$", and at the end the estimate appears
  $$n_d\\ge n/\\log^{d-1}(N)\\,(c_2\\log^4 n)^d$$
  for "some constant $c_2>0$". Neither $c_1$ nor $c_2$ are revealed numerically,
  and their connection with the Lemma 4.2 constants is not parameterized.
  Therefore, without a complete recalculation of Proof Thm. 4.1 cannot be removed
  explicit coefficient in mode $d=\\kappa\\log n/\\log\\log n$
  (base $\\exp=e^x$ in HR notation; replacing with $2^x$ only reduces the threshold).
- `Exact citation:`
  “Suppose we have a refutation of size $N\\le \\exp\\, n^{1/d}/(c_1\\log^4 n)$ for some large
  constant $c_1>0$ …” and later
  “Note that $n_d\\ge n/\\log^{d-1}(N)\\,(c_2\\log^4 n)^d$ for some constant $c_2>0$ …”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:874–877, 929–931`).
- `Status:` barrier certificate (constants $c_1,c_2$ are not extracted without full recalculation).
- `StepID:` Q43.S160-thm41-const-extract.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or write out a full recalculation of Proof Thm. 4.1 (with explicit $c_1,c_2$),
  or accept the barrier and switch to other sources/modes.

-/

/-!
### 16.301. Research step (reduction): plan for recalculating Thm constants. 4.1 via Lemma 4.2 -> Lemma 6.9

- `Lens:` Equivalence.
- `Statement (Q43.S161-thm41-recount-plan):`
  To obtain an explicit coefficient in the mode $d=\\kappa\\log n/\\log\\log n$,
  you need to explicitly fix the constants $c_1,c_2$ from Proof Thm. 4.1.
  This reduces to an explicit constant $A$ in Lemma 4.2, since $A$
  enters into recursion
  $$n_i=\\bigl\\lfloor n_{i-1}/(4A t_{i-1}\\log^4 n_{i-1})\\bigr\\rfloor$$
  and into the probability estimate from which the condition is obtained
  $$\\log N\\le n^{1/d}/(c_1\\log^4 n).$$
  The constant $A$ from Lemma 4.2 in turn depends on the implicit $A_0,A_1,A_2$
  in its proof, and these quantities are derived from the bit count in Lemma 6.9
  (including the terms $A_1|S^*_g|$ and $A_2|S^*_g|$).
  Therefore, the minimum conversion plan is:
  (i) recalculate the bit budget of Lemma 6.9/6.8 with explicit $A_1,A_2$;
  (ii) collect explicit $A_0,A_1,A_2$ in Proof Lemma 4.2 and obtain $A$;
  (iii) output explicit $c_1,c_2$ to Proof Thm. 4.1.
  Base $\\exp=e^x$ (HR notation); replacing it with $2^x$ only reduces the thresholds.
- `Exact citation:`
  recursion $n_i$ and dependence on $A$ - Proof Thm. 4.1
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:889–891`);
  implicit $A_0,A_1,A_2$ -- Proof Lemma 4.2
  (`...:1972–1974, 1996`); explicit $A_1|S^*_g|, A_2|S^*_g|$ -- Proof Lemma 6.9
  (`...:2336–2341`).
- `Status:` reduction (the dependence of $c_1,c_2$ on the Lemma 6.9 constants has been written out).
- `StepID:` Q43.S161-thm41-recount-plan.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or start recalculating Lemma 6.9 with explicit $A_1,A_2$,
  or formally record the impossibility without a complete recount.

-/

/-!
### 16.302. Research step (reduction): recalculation of Lemma 6.9 by $A_1,A_2$ has already been done in Section 16.224-Section 16.225

- `Lens:` Invariant.
- `Statement (Q43.S162-recount-lemma69-bits):`
  The Lemma 6.9 bit budget has already been recalculated using the constants $A_1,A_2$:
  in Section 16.224 received $A_1^{\\mathrm{tot}}=24$ (or $A_1\\le 15$ without signatures),
  and in Section 16.225 $A_2\\le 16$ was obtained for the structures $J_j$ and $I^{*}_{-}$.
  Therefore, the "recount Lemma 6.9 bits" step comes down to using these explicit
  estimates and their substitution in Proof Lemma 4.2 (where $A_0,A_1,A_2$ appear).
  Here $\\exp$ in HR notation is understood as $e^x$; changing the base to $2^x$ has no effect
  on the very fact of the presence of explicit $A_1,A_2$.
- `Exact citation:`
  Lemma 6.9 describes the additional bits $A_1|S^{*}_g|$ and $A_2|S^{*}_g|$
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2336–2341`);
  summing the contributions of Algorithms 2-4 gives $A_1^{\\mathrm{tot}}=24$ (see Section 16.224),
  and parsing the structure $J_j,I^{*}_{-}$ gives $A_2\\le 16$ (see Section 16.225).
- `Status:` reduction (explicit $A_1,A_2$ are fixed; it remains to connect them with $A_0,A_1,A_2$ in Lemma 4.2).
- `StepID:` Q43.S162-recount-lemma69-bits.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` compare $A_1,A_2$ from Lemma 6.9 with the ones of the same name
  constants in Proof Lemma 4.2 and evaluate $A_0$.

-/

/-!
### 16.303. Research step (reduction): constants $A_0,A_1,A_2$ in Proof Lemma 4.2 and their sources

- `Lens:` Equivalence.
- `Statement (Q43.S163-map-lemma42-a0a1a2):`
  In Proof Lemma 4.2, the constants $A_0,A_1,A_2$ appear as a "package" of standard estimates:
  1) $A_0$ comes from Lemma 5.5 when passing to the probability in (16), where
     the multiplier $(A_0\\log n'/\\Delta)^{a+b}$ appears;
  2) $A_1$ absorbs absolute factors in front of the geometric series in $a$
     (including $A^s$ from Lemma 6.9 and numerical constants in (16)-(17));
  3) $A_2$ appears after substitution $b\\le 2a$ (Lemma 6.8) and folding
     sums $\\sum_b \\log^b n'$ in (18).
  Thus, $A_1,A_2$ can be expressed in terms of the explicit $A$ from Lemma 6.9
  and constants from Lemma 5.5; explicitness already rests only on $A_0$.
- `Exact citation:`
  Proof Lemma 4.2: "Using Lemma 5.5 we can bound the probability ..." and
  further (16)-(18) with "for appropriate constants $A_0,A_1,A_2$"
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1975–1979, 1987–1996`);
  connection to Lemma 6.9 - line with $t^a\\Delta^b A^s$ (`...:1972–1974`).
- `Status:` reduction (the origin of $A_0,A_1,A_2$ is localized; explicitness depends on Lemma 5.5).
- `StepID:` Q43.S163-map-lemma42-a0a1a2.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract explicit constant $A_0$ from Lemma 5.5
  (or fix the impossibility without a complete recount).

-/

/-!
### 16.304. Exploratory step (reduction): explicit $A_0$ via Lemma 5.5

- `Lens:` Invariant.
- `Statement (Q43.S164-bound-a0-lemma55):`
  Lemma 5.5 gives
  $$\\frac{|R(k-2s,n,n')|}{|R_{\\mathrm{reg}}(k,n,n')|}
    \\le \\Bigl(\\frac{13C\\log n'}{n/n'}\\Bigr)^{2s}.$$
  Since $\\Delta\\ge n/(6n')$ is used in the same section,
  we have
  $$\\frac{13C\\log n'}{n/n'}\\le \\frac{78C\\log n'}{\\Delta}.$$
  Substituting $2s=a+b$ into the estimate of Proof Lemma 4.2, we can take
  $$A_0:=78C$$
  in the factor $(A_0\\log n'/\\Delta)^{a+b}$ (for odd $a+b$ one can
  use $s=\\lceil(a+b)/2\\rceil$ and absorb the extra
  multiplier in $A_0$). The explicitness of $A_0$ now reduces to the explicitness of $C$.
- `Exact citation:`
  Lemma 5.5: $13C$ coefficient in evaluation
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1353–1363`);
  lower bound $\\Delta\\ge n/(6n')$
  (`...:1401–1402`);
  using the factor $(A_0\\log n'/\\Delta)^{a+b}$ in Proof Lemma 4.2
  (`...:1975–1979`).
- `Status:` reduction (explicit $A_0$ expressed via $C$ from Lemma 5.5).
- `StepID:` Q43.S164-bound-a0-lemma55.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract a numerical estimate for $C$ from Lemma 5.5
  (or fix the barrier at the Chernoff/negative correlation level).

-/

/-!
### 16.305. Research step (barrier certificate): constant $C$ in Lemma 5.5 remains implicit

- `Lens:` Invariant.
- `Statement (Q43.S165-bound-c-lemma55):`
  In the proof of Lemma 5.5, the constant $C$ is chosen to be "large enough" for
  application of Chernoff estimates for negative correlation and subsequent
  union bound. The numerical value of $C$ is not fixed; therefore explicit
  the numerical estimate for $A_0=78C$ (see Section 16.304) is unattainable without complete
  recalculation of Chernoff steps.
- `Exact citation:`
  “Since the Chernoff bounds continue to hold for negatively correlated random variables
  it holds that $X(i,j)\\in(1\\pm0.01)k/n'^2$ except with probability $1/n'^3$ for a large enough
  constant $C>0$.” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1348–1350`)
  and the statement of Lemma 5.5 using $C$ (`...:1353–1354`).
- `Status:` barrier certificate (explicit $C$ is not extracted from the text).
- `StepID:` Q43.S165-bound-c-lemma55.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or recalculate Chernoff steps with explicit constants,
  or accept the barrier and freeze the explicit numerical $A_0$.

-/

/-!
### 16.306. Research step (barrier certificate): explicit $C$ in Lemma 5.5 requires a complete recalculation of the Chernoff step

- `Lens:` Equivalence.
- `Statement (Q43.S166-chernoff-recount):`
  In Lemma 5.5, the constant $C$ is specified as "large enough" via the Chernoff estimate
  for negatively correlated indicators and subsequent union bound.
  The text does not record the numerical value, and it can only be retrieved through
  complete recalculation of Chernoff steps (including constants in the tails for $\delta=0.01$).
  Therefore, an explicit numerical $C$ (and $A_0=78C$) is unattainable without a separate
  full derivational step.
- `Exact citation:`
  “Since the Chernoff bounds continue to hold for negatively correlated random variables
  it holds that $X(i,j)\\in(1\\pm0.01)k/n'^2$ except with probability $1/n'^3$ for a large enough
  constant $C>0$.” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1348–1350`).
- `Status:` barrier certificate (explicit $C$ is not captured).
- `StepID:` Q43.S166-chernoff-recount.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta-constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or carry out a complete recalculation of the Chernoff step with explicit constants,
  or fix $C$ as a parameter and close the numerical part.

-/

/-!
### 16.307. Exploratory step (reduction): freeze $A_0$ as a parameter and continue output

- `Lens:` Equivalence.
- `Statement (Q43.S167-freeze-a0-parameter):`
  In Proof Lemma 4.2, the only implicit factor is $(A_0\\log n'/\\Delta)^{a+b}$,
  where $A_0=78C$ (see Section 16.304). If we take $A_0$ as an external parameter,
  then further steps (summation over $a$, substitution $b\\le 2a$, folding (18))
  give explicit expressions through $A_0,A_1,A_2$. Therefore, Thm. 4.1 turns out
  in a parameterized form with $c_1,c_2$ as functions of $A_0$ without recalculating the Chernoff constants.
- `Exact citation:`
  factor $(A_0\\log n'/\\Delta)^{a+b}$ in Proof Lemma 4.2
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1975–1979`);
  binding $A_0=78C$ to Lemma 5.5 - Section 16.304.
- `Status:` reduction (explicitness reduced to parameter $A_0$).
- `StepID:` Q43.S167-freeze-a0-parameter.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (meta parameters).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` or recalculate the Chernoff step for explicit $C$,
  or use the parameterized version for further analysis.

-/

/-!
### 16.308. Exploratory step (reduction): explicit Chernoff constant $C$ for Lemma 5.4

- `Lens:` Trade-off.
- `Statement (Q43.S168-explicit-c-chernoff):`
  According to Prop. 5 (Dubhashi-Ranjan, 1996) Chernoff-Hoeffding applies to negative
  associated indicators, and Theorem A.16 (Arora-Barak) gives (exp = $e^x$)
  $$\\Pr[|X-\\mu|\\ge\\delta\\mu]\\le 2e^{-\\delta^2\\mu/3}\\quad(0<\\delta\\le 1).$$
  In Lemma 5.4 we have $\\mu=k/n'^2=C\\log n'$ (log = $\\ln$) and $\\delta=0.01$, so
  $$\\Pr[|X-\\mu|\\ge\\delta\\mu]\\le 2e^{-(\\delta^2 C/3)\\log n'}=2\\,n'^{-\\delta^2 C/3}.$$
  For $n'\\ge 2$ it is enough to take $C\\ge 12/\\delta^2=120000$ to
  $\\Pr[|X-\\mu|\\ge\\delta\\mu]\\le 1/n'^3$; then union bound over $n'^2$ squares
  gives probability $\\ge 1-1/n'$. (If $\\log=\\log_2$, then $C$ is multiplied by $\\ln 2$.)
- `Exact citation:`
  Dubhashi–Ranjan (1996), Proposition 5 “(−A and Chernoff–Hoeffding Bounds)”
  (PDF p.7 / printed p.5) - Chernoff for negative association;
  Arora-Barak (2009 draft), Theorem A.16 (PDF p.540) - Chernoff formula.
- `Status:` reduction (explicit $C$ received).
- `StepID:` Q43.S168-explicit-c-chernoff.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (probabilistic constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` propagate explicit $C$ to $A_0=78C$ and check how it affects
  parameters Lemma 4.2 / Thm. 4.1.

-/

/-!
### 16.309. Exploratory step (reduction): explicit $A_0$ and removal of implicit constants

- `Lens:` Equivalence.
- `Statement (Q43.S169-propagate-explicit-a0):`
  From Section 16.308 we take $C\\ge 120000$ (for $\\delta=0.01$, $\\log=\\ln$), so
  $$A_0=78C\\ge 9{,}360{,}000.$$
  Then the factor $(A_0\\log n'/\\Delta)^{a+b}$ in Proof Lemma 4.2 becomes numerically explicit,
  and together with the explicit $A_1,A_2$ from Section 16.302-Section 16.303 this makes the constants $c_1,c_2$ in Thm. 4.1
  fully writeable (albeit very large) without additional hidden assumptions.
- `Exact citation:`
  $A_0=78C$ from Lemma 5.5 (see Section 16.304) + explicit $C$ from Section 16.308;
  where to use $(A_0\\log n'/\\Delta)^{a+b}$ in Proof Lemma 4.2
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1975–1979`).
- `Status:` reduction (implicit constants have been removed; routine arithmetic remains).
- `StepID:` Q43.S169-propagate-explicit-a0.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (numerical constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` write down the explicit $c_1,c_2$ in the formulation of Thm. 4.1 and check
  that further thresholds (for example, $M>2^{n^\\alpha}$) are interpreted correctly.

-/

/-!
### 16.311. Exploratory step (reduction): log/exp base at large$M$ threshold

- `Lens:` Trade-off.
- `Statement (Q43.S171-check-thm41-threshold):`
  HR'22 explicitly states that $\\log$ is taken over base $2$; means threshold
  $$M\\le 2^{n^{\\alpha}},\\qquad \\alpha=\\frac1d-\\frac1{d(d-1)},$$
  in Proof Thm. 4.3 can naturally be read as a power of $2^x$.
  If we use $e^x$, then this is equivalent to replacing
  $n^{\\alpha}\\mapsto (\\ln 2)\\,n^{\\alpha}$ (constant factor in the exponent),
  therefore the asymptotic comparisons Q43 are preserved; for explicit constants
  you need to multiply/divide by $\\ln 2$ when changing the base.
- `Toy test:` for $\\alpha=1/2$ we have $2^{\\sqrt n}=e^{(\\ln 2)\\sqrt n}$,
  that is, the difference is only in the constant factor of the indicator.
- `Exact citation:`
  “Logarithms are denoted by log and are always with respect to the base 2.”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`);
  threshold $M\\le\\exp(n^{\\alpha})$ -- `...:1104–1106` (exp in quote = $2^x$).
- `Status:` reduction (harmonization of logarithmic and exponential bases).
- `StepID:` Q43.S171-check-thm41-threshold.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (change of base - numeric).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` bring all thresholds $M>2^{n^\\alpha}$ in Q43 to base $2$
  and check that explicit $c_1,c_2$ are recalculated in the same base.

-/

/-!
### 16.312. Exploratory step (reduction): matching $\\exp$ as $2^x$ in Q43

- `Lens:` Equivalence.
- `Statement (Q43.S172-exp2-consistency):`
  In the context of HR'22, we accept the $2$ base as the standard choice,
  consistent with $\\log_2$. When passing to $e^x$ it is sufficient to replace
  $x\\mapsto (\\ln 2)\\,x$, that is, explicit constants $c_1,c_2$ and thresholds
  $M>2^{n^\\alpha}$ change only by a factor of $\\ln 2$ in the exponent.
  This does not affect comparisons like "poly vs exp" or the fact that
  $2^{(\\log n)^k}$ is superpolynomial for $k>1$.
- `Toy test:` $2^{(\\log_2 n)^2}=e^{(\\ln 2)(\\log_2 n)^2}$
  and exceeds $n^c$ for any fixed $c$.
- `Exact citation:`
  determining the base of the logarithm - `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`;
  threshold large$M$ in Proof Thm. 4.3 - `...:1104–1106`.
- `Status:` reduction (the exponent base is unified).
- `StepID:` Q43.S172-exp2-consistency.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (numerical change of base).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` recalculate explicit $c_1,c_2$ and all thresholds with $2^{(\\cdot)}$
  in a single base $2$ (for constants, take into account the factors $\\ln 2$).

-/

/-!
### 16.313. Exploratory step (reduction): rescaling $c_1,c_2$ under $\\exp_2$

- `Lens:` Equivalence.
- `Statement (Q43.S173-exp2-c1c2-rescale):`
  Let's move on to the agreement $\\exp_2(x):=2^x$ and $\\log=\\log_2$.
  Then the explicit constants from Section 16.310 are already consistent with the $2$ base (they are obtained
  from bit encoding and $\\log_2$), and the Proof Thm formula. 4.1 reads as
  $$N\\le 2^{\\,n^{1/d}/(c_1\\log_2^4 n)}\\qquad\\text{and}\\qquad
    n_d\\ge \\frac{n}{\\log_2^{d-1}N\\cdot(c_2\\log_2^4 n)^d}.$$
  If you need to use $e^x$ and $\\ln$, then the constants are recalculated
  explicitly: $c_1^{(e)}=c_1/(\\ln 2)^5$ (taking into account the replacement $\\log_2^4 n$) and
  $c_2^{(e)}=c_2/(\\ln 2)^4$ (plus the factor $(\\ln 2)^{-(d-1)}$,
  which can be absorbed into $c_2$ for a fixed $d$).
  For asymptotics this is equivalent; in particular,
  $\\exp_2((\\log_2 n)^k)=2^{(\\log_2 n)^k}$ is superpolynomial for $k>1$.
- `Toy test:` for $d=1$ from $\\log_2 N\\le n/(c_1\\log_2^4 n)$ we obtain
  $N\\le 2^{n/(c_1\\log_2^4 n)}$, and when moving to $e^x$ the indicator changes
  by the factor $\\ln 2$.
- `Exact citation:`
  logarithm base - `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`;
  threshold large$M$ in Proof Thm. 4.3 - `...:1104–1106`.
- `Status:` reduction (explicit $c_1,c_2$ are consistent with $\\exp_2$).
- `StepID:` Q43.S173-exp2-c1c2-rescale.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (change of base - numeric).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` carry out a single pass through Q43 and replace everything
  $2^{(\\cdot)}$ and related thresholds on a single base $2$.

-/

/-!
### 16.315. Exploratory step (exact citation): base-2 markings in citations with `exp`

- `Lens:` Equivalence.
- `Statement (Q43.S175-exp2-quote-annotation):`
  In HR'22/Hastad'20 citations where used `exp(…)`, added explicit marks,
  what should be read in the context of $\\log_2$ `exp` like $2^x$; this eliminates
  ambiguity of the base in places where we retain a direct quote.
- `Exact citation:`
  HR’22 Proof Thm. 4.3 (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1104–1106`)
  and Hastad'20 Thm. 6.5 (`resources/text_cache/hastad_2020_small_depth_frege_tseitin_grids.txt:825–827`).
- `Status:` exact citation (marks to citations, without changing formulas).
- `StepID:` Q43.S175-exp2-quote-annotation.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (comments on quotes).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` agree on similar notes in other sections,
  where are direct quotes saved? `exp`.

-/

/-!
### 16.316. Exploratory step (exact citation): sweep expcitations with an explicit base

- `Lens:` Compression/canonization.
- `Statement (Q43.S176-exp2-quote-sweep):`
  For all direct quotes from `exp(…)` in Q43 the base ($2^x$) is now explicitly indicated next to the link,
  and the only "exponent in quotes" is outside Q43 (the formula "solve $M=2^{O(n^{1/(d-1)})}$" in Section 16.142)
  reduced to the form $2^{(\\cdot)}$ to remove ambiguity.
- `Exact citation:`
  HR’22 Proof Thm. 4.3 (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1104–1106`);
  Håstad’20 Thm. 6.5 (`resources/text_cache/hastad_2020_small_depth_frege_tseitin_grids.txt:825–827`).
- `Status:` exact citation (explicit basis for citations with `exp`).
- `StepID:` Q43.S176-exp2-quote-sweep.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (comments on quotes).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check if there are any citations left with `exp` outside Q43 (e.g. in Q39/Q16.x),
  and, if necessary, fix the base next to the citation.

-/

/-!
### 16.317. Research step (exact citation): scan core citations with `exp` and fixing the base $2^x$

- `Lens:` Equivalence.
- `Statement (Q43.S177-exp2-quote-scan-core):`
  In Section 16.92 (`formal/Notes/TseitinCore.lean`) Thm formulation. 6.5 (Hastad'20)
  recorded in the $2$ database and marked "`exp` in source = $2^x$";
  this closes the direct `exp`-quote outside Q43 without changing the asymptotics.
- `Exact citation:`
  Håstad’20 Thm. 6.5 (`resources/text_cache/hastad_2020_small_depth_frege_tseitin_grids.txt:825–827`;
  see also `../../resources/downloads/hastad_2020_small_depth_frege_tseitin_grids.pdf`).
- `Status:` exact citation (exponent base fixed as $2^x$).
- `StepID:` Q43.S177-exp2-quote-scan-core.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (comments on quotes).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check if direct quotes remain from `exp` V `formal/Notes/TseitinCore.lean`
  and in summary files, and if necessary, cast to the base $2$ or explicitly specify $e^x$.

-/

/-!
### 16.318. Exploratory step (exact citation): scan remaining expcitations in core/summary

- `Lens:` Compression/canonization.
- `Statement (Q43.S178-exp2-quote-scan-remaining):`
  IN `formal/Notes/TseitinCore.lean` exponential estimates referring to
  Itsykson-Oparin'13 and Razborov'23, are reduced to the form $2^{(\cdot)}$,
  and in the summary files the same databases are consistent. This fixes the interpretation `exp`
  as $2^x$ for the corresponding quotes (changing the base gives only a constant factor in the indicator).
- `Exact citation:`
  Itsykson–Oparin 2013, Cor. 1 + Thm. 1
  (`../../resources/downloads/itsykson_oparin_2013_tseitin.pdf`);
  Razborov 2023, Thm. 6.8
  (`../../resources/downloads/razborov_2023_proof_complexity_eseepdf`);
  Pitassi–Rossman–Servedio–Tan 2016, Thm. 1
  (`../../resources/downloads/pitassi_rossman_servedio_tan_2016_expander_switching_lemma.pdf`).
- `Status:` exact citation (base $2^x$ is fixed for core/summary formulas).
- `StepID:` Q43.S178-exp2-quote-scan-remaining.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (comments on quotes).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` go through the rest `exp(…)` V `formal/Notes/TseitinCore.lean`
  (especially analytic places with $\\ln$) and explicitly note where $e^x$.

-/

/-!
### 16.319. Research step (exact citation): analytical `exp(…)` -> explicit $e^x$ in core

- `Lens:` Equivalence.
- `Statement (Q43.S179-exp2-quote-scan-analytic):`
  In analytical places `formal/Notes/TseitinCore.lean` (optimization $f(d)=dX^{2/d}$)
  all the remaining ones `exp(…)` replaced by explicit $e^{(\cdot)}$, and in the proof
  It is fixed that the natural logarithm $\\ln$ is used.
  This disambiguates the base in the asymptotics (especially in steps with $\\ln X$).
- `Exact citation:`
  Galesi-Itsykson-Riazanov-Sofronova 2019, Claim 28 (section 4.3),
  `../../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`
  (used for the formula $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$, then analytical optimization is carried out).
- `Status:` exact citation (base $e^x$ is explicitly specified for analytical steps).
- `StepID:` Q43.S179-exp2-quote-scan-analytic.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation in analytics).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` go through places with $\\log$ in analytical sections and solve
  where you need to leave $\\log_2$ vs $\\ln$ (without affecting the asymptotics).

-/

/-!
### 16.320. Research step (exact citation): log base in GIRS-upper analytics

- `Lens:` Equivalence.
- `Statement (Q43.S180-exp2-quote-scan-logbases):`
  In analytical places GIRSupper (`formal/Notes/TseitinCore.lean` §16.119–§16.121)
  the base of logarithms is made explicit: in transitions of the form $2^{\\log X}=X$ $\\log_2$ is used,
  and in optimization through $L:=\\ln X$ the natural logarithm is preserved.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` exact citation (log base is marked; asymptotics does not change).
- `StepID:` Q43.S180-exp2-quote-scan-logbases.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` scan remaining $\\log$ in core and reduce to $\\log_2$/$\\ln$ if necessary.

-/

/-!
### 16.321. Exploratory step (exact citation): log_2 in PRST'16 depth-vs-size toy-test

- `Lens:` Compression/canonization.
- `Statement (Q43.S181-exp2-quote-scan-logbases-remaining):`
  In Section 16.96 (PRST'16 Thm. 1) for expressions of the form $2^{(\\log n)^2}$ and $n^{\\Omega((\\log n)/d^2)}$
  the base $\\log_2$ is explicitly fixed; this is consistent with the explicit use of $\\log_2 n$
  in PRST'16 (Lemma 2.7), and disambiguates the interpretation of $2^{(\\log n)^2}$.
- `Exact citation:`
  Pitassi-Rossman-Servedio-Tan 2016, Lemma 2.7 uses $\\log_2 n$,
  `../../resources/downloads/pitassi_rossman_servedio_tan_2016_expander_switching_lemma.pdf`.
- `Toy test:` $2^{(\\log_2 n)^k}$ is superpolynomial for $k>1$; for example $2^{(\\log_2 n)^2}=n^{\\log_2 n}$.
- `Status:` exact citation (the log database is noted in the toy evaluation).
- `StepID:` Q43.S181-exp2-quote-scan-logbases-remaining.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` go through the remaining $\\log$ in core/summary with $2^{(\\cdot)}$ and lead to $\\log_2$/$\\ln$ if necessary.

-/

/-!
### 16.322. Research step (reduction): log_2 in $2^{\\mathrm{poly}(\\log)}$ in core/summary

- `Lens:` Equivalence.
- `Statement (Q43.S182-exp2-quote-scan-logbases-core-sweep):`
  In core/summary places with $2^{\\mathrm{poly}(\\log S)}$ and $2^{O(\\cdot\\log n)}$
  the logarithm is explicitly reduced to $\\log_2$ (in accordance with the $\\exp_2$convention), and in analytics
  optimization $f(d)$ remains $\\ln$.
- `Reduction:` according to the formula for changing the base $\\log_a n=\\log_2 n/\\log_2 a$ any record of the form
  $2^{\\mathrm{poly}(\\log_a n)}$ is equivalent to $2^{\\mathrm{poly}(\\log_2 n)}$ with changing constants.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in exponents).
- `StepID:` Q43.S182-exp2-quote-scan-logbases-core-sweep.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` continue sweeping the remaining $\\log$ in core/summary outside Q43blocks.

-/

/-!
### 16.323. Exploratory step (reduction): log_2 in summary `docs/15_proof_complexity.md`

- `Lens:` Compression/canonization.
- `Statement (Q43.S183-exp2-quote-scan-logbases-summary-sweep):`
  In summary blocks `docs/15_proof_complexity.md` all mentions of $\\log$,
  included in the depth thresholds and HR checks are reduced to $\\log_2$;
  this synchronizes the summary with the $\\exp_2$convention and with the $\\log_2$ base in HR'22.
- `Reduction:` according to the base change formula $\\log_a n=\\log_2 n/\\log_2 a$ replacement $\\log\\to\\log_2$
  preserves asymptotics in the $O(\\log n/\\log\\log n)$ and $2^{\\mathrm{poly}(\\log n)}$ modes.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S183-exp2-quote-scan-logbases-summary-sweep.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` scan the remaining summary sections outside Section 15 and, if necessary,
  bring $\\log$ to $\\log_2$/$\\ln$.

-/

/-!
### 16.324. Research step (reduction): log_2 in summary outside Section 15 (switching lemma)

- `Lens:` Equivalence.
- `Statement (Q43.S184-exp2-quote-scan-logbases-summary-remaining):`
  In the summary section `docs/11_switching_lemma_ac0.md` logarithms in output
  $S\\ge 2^{\\Omega(n^{1/(k-1)})}$ are reduced to $\\log_2 S$,
  so that formulas with $2^{(\\cdot)}$ are consistent with the $\\exp_2$convention.
- `Reduction:` replacing $\\log\\to\\log_2$ changes the constant in bigO and does not affect
  asymptotics of thresholds of the form $O(\\log n)$ and $2^{\\Omega((\\log n)^k)}$.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S184-exp2-quote-scan-logbases-summary-remaining.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` complete the sweep on the remaining summary files outside Section 15/Section 11.

-/

/-!
### 16.325. Research step (reduction): log_2 in summary outside Section 15/Section 11 (PCP, Savitch)

- `Lens:` Compression/canonization.
- `Statement (Q43.S185-exp2-quote-scan-logbases-summary-final):`
  In summary sections `docs/16_ip_pcp.md` and `docs/13_savitch.md` logarithms in estimates,
  associated with binary counting and exponent are reduced to $\\log_2$ (for example,
  $r(n)=O(\\log_2 n)$ and $\\log_2 M=O(s(n))$).
- `Reduction:` the replacement $\\log\\to\\log_2$ preserves the asymptotics and harmonizes the entries
  with binary interpretation $2^{(\\cdot)}$.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S185-exp2-quote-scan-logbases-summary-final.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` confirm the absence of remaining ambiguity by $\\log$ in summary,
  or fix a point where the base is unimportant.

-/

/-!
### 16.326. Research step (reduction): log_2 in summary outside Section 15/Section 11 (time hierarchy)

- `Lens:` Equivalence.
- `Statement (Q43.S186-exp2-quote-scan-logbases-summary-tail):`
  In the summary section `docs/12_time_hierarchy.md` logarithms in estimates
  universal simulation and hierarchy theorems are reduced to $\\log_2$,
  to reconcile the entries with the binary interpretation of $2^{(\\cdot)}$.
- `Reduction:` changing the base $\\log\\to\\log_2$ changes only the constants in $O(\\cdot)$
  and does not affect the strictness of inclusions.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S186-exp2-quote-scan-logbases-summary-tail.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check the remaining summary files on ambiguity using $\\log$,
  or fix that the base is everywhere insignificant.

-/

/-!
### 16.327. Research step (reduction): log/ln in summaryaudit (circuit complexity)

- `Lens:` Equivalence.
- `Statement (Q43.S187-exp2-quote-scan-logbases-summary-audit):`
  In the summary section `docs/09_circuit_complexity.md` logarithms are consistent as
  $\\ln$ in Razborov'85 lower estimate (to avoid mixing $\\ln$ and $\\log$).
- `Reduction:` changing the logarithm base in expressions of the form $m^{C\\log m}$ is absorbed
  into the constant $C$, so explicitly specifying $\\ln$ does not change the asymptotics.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S187-exp2-quote-scan-logbases-summary-audit.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` complete audit of summary logarithms and commit,
  that the remaining bases are insignificant.

-/

/-!
### 16.328. Research step (reduction): log_2 in summaryaudit (basic inclusions)

- `Lens:` Compression/canonization.
- `Statement (Q43.S188-exp2-quote-scan-logbases-summary-closeout):`
  In the summary section `docs/03_basic_inclusions.md` logarithms for counters and
  Savitch templates are reduced to $\\log_2$ (log2 -> log_22), matching the base with the binary count.
- `Reduction:` changing the base $\\log\\to\\log_2$ changes only the constants and has no effect
  on polynomial memory.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of the base in summary).
- `StepID:` Q43.S188-exp2-quote-scan-logbases-summary-closeout.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` state that the remaining $\\log$ in the summary is unimportant
  (or note exceptions).

-/

/-!
### 16.329. Research step (reduction): postaudit summarylogarithms

- `Lens:` Equivalence.
- `Statement (Q43.S189-exp2-quote-scan-logbases-summary-postaudit):`
  In summary files `docs/03_basic_inclusions.md`, `docs/09_circuit_complexity.md`,
  `docs/11_switching_lemma_ac0.md`, `docs/12_time_hierarchy.md`,
  `docs/13_savitch.md`, `docs/15_proof_complexity.md`, `docs/16_ip_pcp.md`
  all remaining logarithms either have an explicit base $\\log_2$ or are in the forms
  $O(\\log n)$/$O(N\\log N)$, where changing the base changes only the constant.
- `Reduction:` the base $\\log$ affects only the multiplicative constant, so
  in asymptotics of the type $O(\\log n)$ and $O(N\\log N)$ the log base is unimportant.
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (postaudit: remaining logs are base‑agnostic).
- `StepID:` Q43.S189-exp2-quote-scan-logbases-summary-postaudit.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` close Q43 log database audit if necessary
  or note isolated exceptions.

-/

/-!
### 16.330. Research step (reduction): exit logbase audit to summary

- `Lens:` Equivalence.
- `Statement (Q43.S190-exp2-quote-scan-logbases-summary-exit):`
  Postaudit complete: remaining summary estimates use either explicit $\\log_2$,
  or the form $O(\\log n)$/$O(N\\log N)$, where changing the base changes only the constant.
  In subsequent edits, any exponential forms will be written as
  $2^{(\\cdot)}$ or $e^{(\\cdot)}$.
- `Reduction:` log audit completed; Q43 returns to the substantive question
  about cost$t$ evaluations in flat localEF(s).
- `Exact citation:`
  HR'22 fixes the convention `log=log_2` (“Logarithms are denoted by log and are always with respect to the base 2.”),
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (audit exit).
- `StepID:` Q43.S190-exp2-quote-scan-logbases-summary-exit.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` start the meaningful step on Q43: either cost$t$ construction scheme
  evaluations for each line, or the exact point of failure (nesting/global support).

-/

/-!
### 16.331. Research step (reduction): pivot - the size of the formula after expanding the extension variables

- `Lens:` Trade-off.
- `Statement (Q43.S191-flat-eval-construction-pivot):`
  In flat localEF(s) when expanding $p_i\\leftrightarrow\\varphi_i(X)$ in line $F$
  the size of the formula in $X$ is estimated as
  $$M(F)\\le |F| + \\sum_{p_i\\in \\mathrm{vars}(F)} \\#_F(p_i)\\cdot|\\varphi_i|.$$
  Therefore, if for all $i$ $|\\varphi_i|\\le \\mathrm{poly}(s)$ holds and
  $|F|=\\mathrm{poly}(n)$, then $M(F)\\le \\mathrm{poly}(s)\\cdot \\mathrm{poly}(n)$,
  and the parameter HR $t=\\log_2 M(F)$ remains $O(\\log n+\\log s)$.
- `Reduction:` constructing cost$t$ evaluations for flat localEF(s) strings reduces to
  control over the size of formulas $|\\varphi_i|$ (or to an alternative estimate of $M(F)$ without
  deployment); without such an estimate $M(F)$ can be arbitrarily large even with
  $|\\mathrm{supp}(\\varphi_i)|\\le s$.
- `Toy‑test:` if $F$ contains $m$ copies of $p$ and $|\\varphi|=2^{(\\log_2 n)^2}$,
  then $M(F)=m\\cdot 2^{(\\log_2 n)^2}$ and $t=\\log_2 m + (\\log_2 n)^2$
  (the form $2^{(\\log_2 n)^2}$ is superpolynomial).
- `Status:` reduction (pivot: the size of the formula after expansion is the bottleneck).
- `StepID:` Q43.S191-flat-eval-construction-pivot.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure calculation of the size of the formula).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` fix the required constraint on $|\\varphi_i|$
  (e.g. $|\\varphi_i|\\le \\mathrm{poly}(s)$ as part of the localEF(s) model)
  or propose an eval design that does not depend on full deployment.

-/

/-!
### 16.332. Exploratory step (reduction): axiom-size bound via line size in flat local-EF(s)

- `Lens:` Trade-off.
- `Statement (Q43.S192-flat-eval-axiom-size-bound):`
  Let there be a flat local-EF(s) proof of size $S$, where the size of the line is measured by the number
  characters/literals and each extension axiom is written as a string
  $p_i\\leftrightarrow\\varphi_i(X)$.
  Then for any string $F$:
  $$M(F)\\le |F| + \\sum_{p_i\\in\\mathrm{vars}(F)} \\#_F(p_i)\\cdot|\\varphi_i|
           \\le |F| + |F|\\cdot \\max_i |\\varphi_i|
           \\le S + S^2,$$
  and therefore $t=\\log_2 M(F)=O(\\log_2 S)$. If $S=\\mathrm{poly}(n)$, then $t=O(\\log_2 n)$.
- `Reduction:` control of $|\\varphi_i|$ is reduced to a standard limit on the size of lines;
  the additional condition $|\\varphi_i|\\le \\mathrm{poly}(s)$ is needed only if
  extension axioms are considered "free".
- `Toy-kill:` if the axioms are not taken into account in size, one can take
  $|\\varphi_i|=2^{(\\log_2 n)^2}$ for $|\\mathrm{supp}(\\varphi_i)|\\le s$ and get
  $t=(\\log_2 n)^2+O(\\log_2 |F|)$, which is superpolynomial.
- `Status:` reduction (axiom-size bound = line-size bound in the standard metric).
- `StepID:` Q43.S192-flat-eval-axiom-size-bound.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure counting of string/substitution sizes).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check whether extension axioms are taken into account in the size of the local-EF(s) model;
  if not, fix it as a barrier or strengthen the model with an explicit restriction on
  $|\\varphi_i|$.

-/

/-!
### 16.333. Exploratory step (reduction): axiom-size accounting vs line-count in flat local-EF(s)

- `Lens:` Equivalence.
- `Statement (Q43.S193-flat-eval-axiom-size-accounting):`
  If the size of the proof $S$ is measured by the total size of the strings (sum of lengths/literals),
  then each line has size $\\le S$, in particular $|\\varphi_i|\\le S$ for any
  extension axioms $p_i\\leftrightarrow\\varphi_i(X)$. Then $M(F)\\le S+S^2$ and
  $t=\\log_2 M(F)=O(\\log_2 S)$, as in Section 16.332.
  If $S$ is only the number of lines, then $|\\varphi_i|$ is not limited by the size of the proof,
  and control of $t$ requires an additional constraint on $|\\varphi_i|$.
- `Reduction:` Q43 comes down to the choice of size metric in the local-EF(s) model:
  line-size gives an automatic bound on $|\\varphi_i|$, line-count requires an explicit bound
  or a separate barrier.
- `Toy-check:` with line-count you can take a proof from one line
  $p\\leftrightarrow\\varphi(X)$ with $|\\varphi|=2^{(\\log_2 n)^2}$, and then
  $t=(\\log_2 n)^2$ is superpolynomial.
- `Status:` reduction (accounting: line-size vs line-count).
- `StepID:` Q43.S193-flat-eval-axiom-size-accounting.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (pure calculation of the size of the evidence).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` clarify which size metric is used in the definition of local-EF(s)
  and in what places "free" extension axioms are allowed.

-/

/-!
### 16.334. Research step (exact citation): line-size M in HR'22 Theorem 4.3

- `Lens:` Invariant.
- `Statement (Q43.S194-flat-eval-axiom-size-model-check):`
  In HR'22, the parameter $M$ is specified as the size of the line (formula), and $N$ is the number of lines;
  this fixes the "line-size" metric and eliminates the "size = number of lines" interpretation.
- `Exact citation:`
  Håstad–Risse (2022), "Tseitin formulas on the grid are hard for bounded depth Frege",
  Theorem 4.3 (paper p. 16; PDF p. 18): "If each line of the refutation is of size M and depth d..."
  and further: "refutation ... consisting of N lines, where each line is a formula of size M".
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:938-963`.
  (In the article log = log_2, so exp in the wording is read as 2^x.)
- `Reduction:` to transfer HR parameters to flat local-EF(s), you need to measure the line size
  by formula size and consider extension axioms as strings; line-count does not capture $M$.
- `Status:` exact citation (size metric pinned).
- `StepID:` Q43.S194-flat-eval-axiom-size-model-check.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (exact quote).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` explicitly capture the size metric in the definition of local-EF(s)
  (line-size vs line-count) or mark a barrier with "free" extension axioms.

-/

/-!
### 16.335. Exploratory step (reduction): size metric for flat local-EF(s)

- `Lens:` Compression/canonization.
- `Statement (Q43.S195-flat-eval-axiom-size-definition):`
  We fix the size metric flat local-EF(s) as a pair $(N,M)$, where $N$ is the number of lines,
  and $M$ is the maximum size of the line (formula). Extension axioms
  $p_i\\leftrightarrow\\varphi_i(X)$ are considered strings, so $|\\varphi_i|\\le M$.
  Then $t=\\log_2 M$, and with a general estimate of $S$ for the total size of the proof
  we have $M\\le S$ and $t=O(\\log_2 S)$.
- `Reduction:` this fits the model with HR'22 Thm. 4.3 (line-size $M$ and line-count $N$)
  and excludes "free" extension axioms; all Q43 steps are read with the $M$ parameter.
- `Toy-check:` if we consider only the number of rows, then $M$ is not controlled
  (one line with $|\\varphi|=2^{(\\log_2 n)^2}$ gives $t=(\\log_2 n)^2$).
- `Status:` reduction (size metric is fixed).
- `StepID:` Q43.S195-flat-eval-axiom-size-definition.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (metric definition).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` if necessary, fix the size metric in the core definitions
  and check how it affects the formal statements of Q43 (t = log_2 M).

-/

/-!
### 16.336. Research step (proof): formalization of the size metric (N,M)

- `Lens:` Invariant.
- `Statement (Q43.S196-flat-eval-size-metric-formalize):`
  IN `formal/WIP/Work.lean` definitions of metrics line-size/line-count/line-max have been introduced
  and the lemma is proven: if a string is included in proof, then its size does not exceed the total
  proof size (line-size <= proofSize).
- `Proof (Lean):`
  definitions `Q43_lineSize`, `Q43_proofSize`, `Q43_lineCount`, `Q43_lineMax` and
  lemma `Q43_lineSize_le_proofSize` (see `formal/WIP/Work.lean`).
- `Status:` proof (Lean code compiles).
- `StepID:` Q43.S196-flat-eval-size-metric-formalize.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (definitions/arithmetic of naturals).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` associate parameters (N,M) with `t=log_2 M` and write down the dependency
  eval thresholds in terms of these definitions.

-/

/-!
### 16.337. Exploratory step (proof): parameter t as log_2 M

- `Lens:` Equivalence.
- `Statement (Q43.S197-flat-eval-size-metric-tparam):`
  IN `formal/WIP/Work.lean` the parameter $t:=\\log_2 M$ is introduced as `Nat.log2 M` and proven
  basic estimate $t\\le M$ (Lemma `Q43_tParam_le`), which captures the string size relationship
  and depth parameter evaluation.
- `Proof (Lean):`
  definitions `Q43_tParam` and lemma `Q43_tParam_le` (see `formal/WIP/Work.lean`).
- `Status:` proof (Lean code compiles).
- `StepID:` Q43.S197-flat-eval-size-metric-tparam.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (natural arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` use $t=\\log_2 M$ in formal formulations of Q43 and
  associate $M$ with proofSize via lineMax/lineSize.

-/

/-!
### 16.338. Research step (proof): t=log_2 M <= proofSize

- `Lens:` Equivalence.
- `Statement (Q43.S198-flat-eval-tparam-usage):`
  IN `formal/WIP/Work.lean` it has been proven that $\\mathrm{lineMax}(\\pi)\\le\\mathrm{proofSize}(\\pi)$,
  which means $t=\\log_2(\\mathrm{lineMax}(\\pi))\\le\\mathrm{proofSize}(\\pi)$.
  This relates the parameter $t$ to the total size of the evidence.
- `Proof (Lean):`
  lemmas `Q43_lineMax_le_proofSize` and `Q43_tParam_le_proofSize` (see `formal/WIP/Work.lean`).
- `Status:` proof (Lean code compiles).
- `StepID:` Q43.S198-flat-eval-tparam-usage.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (natural arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` use this connection in formal estimates of $t$ for Q43
  (for example, $t=O(\\log_2 S)$ with $S=\\mathrm{proofSize}$).

-/

/-!
### 16.339. Research step (proof): t <= log_2 proofSize

- `Lens:` Equivalence.
- `Statement (Q43.S199-flat-eval-tparam-ologs):`
  IN `formal/WIP/Work.lean` it is proved that $\\log_2$ is monotonic on Nat and
  $t=\\log_2(\\mathrm{lineMax})\\le\\log_2(\\mathrm{proofSize})$; this gives an explicit
  the relation $t \\le \\log_2 S$ when $S=\\mathrm{proofSize}$.
- `Proof (Lean):`
  lemmas `Q43_log2_mono` and `Q43_tParam_le_log2_proofSize` (see `formal/WIP/Work.lean`).
- `Status:` proof (Lean code compiles).
- `StepID:` Q43.S199-flat-eval-tparam-ologs.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (natural arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` if necessary, print an explicit bound $t\\le c\\log_2 n$
  for polynomial $S$ and use it in Q43 estimates.

-/

/-!
### 16.340. Research step (reduction): t = O(log_2 n) with S = poly(n)

- `Lens:` Trade-off.
- `Statement (Q43.S200-flat-eval-tparam-ologn):`
  If the total proof size $S(n)$ is polynomial, i.e.
  $S(n)\\le n^k+1$ for some $k$, then from $t\\le\\log_2 S$ it follows
  $t=O(\\log_2 n)$: for $n\\ge 2$ we have $S\\le 2n^k$, which means
  $$t\\le\\log_2 S\\le 1 + k\\log_2 n.$$
- `Reduction:` the Q43 link now goes like this:
  line-size $M\\le S$  $t=\\log_2 M\\le\\log_2 S$  at $S=\\mathrm{poly}(n)$
  we get $t=O(\\log_2 n)$ (logarithm base 2).
- `Toy-check:` for $S=n^k$ we obtain exactly $t=\\log_2 S=k\\log_2 n$.
- `Status:` reduction (polynomial size  logarithmic t).
- `StepID:` Q43.S200-flat-eval-tparam-ologn.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (asymptotic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` write down the explicit parametric mode $t\\le c\\log_2 n$
  in the formulations of Q43 and check compatibility with HR assessments.

-/

/-!
### 16.341. Research step (reduction): polylog t of quasi-poly size

- `Lens:` Equivalence.
- `Statement (Q43.S201-flat-eval-tparam-polylogn):`
  If the total size of the proof is quasi-polynomial, for example
  $$S(n)\\le n^{(\\log_2 n)^c}=2^{(\\log_2 n)^{c+1}},$$
  then from $t\\le\\log_2 S$ it follows
  $$t\\le (\\log_2 n)^{c+1},$$
  that is, $t=\\mathrm{polylog}(n)$ (base 2 logarithm).
  For $c\\ge 1$ the growth of $2^{(\\log_2 n)^{c+1}}$ is superpolynomial.
- `Reduction:` mode $S= n^{\\mathrm{polylog}(n)}$ gives $t=\\mathrm{polylog}(n)$,
  which is compatible with Q43 requirements for small evaluations.
- `Toy-check:` for $S=2^{(\\log_2 n)^2}$ we obtain $t\\le(\\log_2 n)^2$.
- `Status:` reduction (quasi-poly size => polylog t).
- `StepID:` Q43.S201-flat-eval-tparam-polylogn.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: not applicable (asymptotic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` associate polylog-$t$ mode with HR compatibility
  (for example, check the conditions $t(d)\\le n_d/16$ for $t=(\\log_2 n)^{O(1)}$).

-/

/-!
### 16.342. Exploratory step (reduction): polylog-$t$ is compatible with HR after $t'=(2s+1)t$

- `Lens:` Equivalence.
- `Statement (Q43.S202-flat-eval-hr-compat-polylog):`
  In flat localEF(s), $P$query expansion replaces the depth parameter
  $t$ by $t':=(2s+1)t$ (see Section 16.165). If $s(n)$ and $t(n)$ are polylog$(n)$
  (logarithm of base $2$), then $t'(n)$ remains polylog$(n)$, and all HR checks
  are reduced to monitoring thresholds of the form $t'(n)\\le n/16$, $s(n)\\le n/32$.
- `Reduction:` HR parameters depend on depth only through $t$; means for Q43
  it is enough to connect $t$ and $t'$ and check that the polylog mode does not break
  $n_\\eta$ recursion (up to polylog factors).
- `Toy‑check:` $s=0$ gives $t'=t$; for $s=\\log_2 n$ we have
  $t'\\le(2\\log_2 n+1)\\,t=O((\\log_2 n)^2)$.
- `Attempt to "kill":` if $s(n)=2^{\\sqrt{\\log_2 n}}$ (base $2$), then $t'$ is already
  super-polylog and HR-recursion may collapse; means the hypothesis "$s$ polylog"
  significant.
- `Status:` reduction (polylog mode is stable at $t'=(2s+1)t$).
- `StepID:` Q43.S202-flat-eval-hr-compat-polylog.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure parameter arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check the exact place in HR Lemma 4.5 where required
  $t(\\eta)\\le n_\\eta/16$, and estimate the stock after replacing $t\\mapsto t'$.

-/

/-!
### 16.343. Exploratory step (reduction): HR threshold $t'\\le n/16$ from polylog mode

- `Lens:` Invariant.
- `Statement (Q43.S203-flat-eval-hr-param-check):`
  Let $t'(n)\\le(\\log_2 n)^a$ and $s(n)\\le(\\log_2 n)^b$ for fixed $a,b$.
  Then there exists $n_0(a,b)$ such that for all $n\\ge n_0$
  $t'(n)\\le n/16$ and $s(n)\\le n/32$.
- `Reduction:` checking the HR conditions $t'\\le n/16$ and $s\\le n/32$ reduces to
  choosing $n$ large enough and then checking that the recursion $n_\\eta$
  does not fall below $n_0$.
- `Toy‑check:` for $n=2^{24}$ we have $\\log_2 n=24$ and for $a\\le4$ we get
  $24^a\\le 2^{24}/16$.
- `Attempt to "kill":` if the powers of polylog are not fixed (or $s(n)=2^{\\sqrt{\\log_2 n}}$),
  then the condition $t'\\le n/16$ may fail; this means that fixing $a,b$ is critical.
- `Status:` reduction (threshold conditions are reduced to "$n$ is large enough").
- `StepID:` Q43.S203-flat-eval-hr-param-check.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (parameter arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` pass the threshold through the recursion HR $n_\\eta$ and show that
  $t'(\\eta)\\le n_\\eta/16$ is maintained at all levels.

-/

/-!
### 16.344. Exploratory step (reduction): threshold $t'(\\eta)\\le n_\\eta/16$ via HR recursion

- `Lens:` Trade-off.
- `Statement (Q43.S204-flat-eval-hr-neta-threshold):`
  In HR recursion $n_\\eta=\\lfloor n_{\\eta-1}/(A\\,t'\\,\\log_2^{c_1} n_{\\eta-1})\\rfloor$
  for $t'(n)=\\mathrm{polylog}(n)$ there is $n_0$ and a horizon $\\eta_*$ such that
  for all $\\eta\\le\\eta_*$ we have $n_\\eta\\ge n_0$, which means
  $t'(\\eta)\\le n_\\eta/16$ and $s(\\eta)\\le n_\\eta/32$.
- `Reduction:` HR checks at all levels are reduced to a clear lower limit
  $n_\\eta\\ge n_0$; this is achieved if the recursion divides by the polylog factor
  only $O(\\log n)$ steps.
- `Toy‑check:` for $n=2^{24}$ and $t'(n)=\\log_2^4 n$ we have
  $A\\,t'\\,\\log_2^{c_1}n\\le\\log_2^{O(1)}n$, so $n_1\\ge 2^{24}/\\log_2^{O(1)}n$
  and the threshold $t'\\le n_1/16$ is preserved.
- `Attempt to "kill":` if $t'(n)=2^{\\sqrt{\\log_2 n}}$ (base $2$), then the divisor is already
  is subexponential, and $n_\\eta$ can fall below $n_0$ in $O(1)$ steps.
- `Status:` reduction (threshold conditions are reduced to $n_\\eta$ control).
- `StepID:` Q43.S204-flat-eval-hr-neta-threshold.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (parametric recursion).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` formalize an explicit lower bound $n_\\eta\\ge n/\\log_2^{O(\\eta)} n$
  and derive from it $t'(\\eta)\\le n_\\eta/16$ for all HR levels.

-/

/-!
### 16.345. Exploratory step (reduction): explicit lower bound $n_\\eta$

- `Lens:` Invariant.
- `Statement (Q43.S205-flat-eval-hr-neta-recursion):`
  Let $t'(m)\\le(\\log_2 m)^a$ and the recursion HR has the form
  $$n_\\eta=\\Bigl\\lfloor\\frac{n_{\\eta-1}}{A\\,t'(n_{\\eta-1})\\,\\log_2^{c_1} n_{\\eta-1}}\\Bigr\\rfloor,$$
  then for $n_{\\eta-1}\\ge 2$ and monotonicity of $t'$ in $m$ we obtain
  $$n_\\eta\\ge \\frac{n_{\\eta-1}}{A\\,\\log_2^{a+c_1} n_{\\eta-1}}
  \\ge \\frac{n}{\\bigl(A\\,\\log_2^{a+c_1} n\\bigr)^\\eta}.$$
- `Reduction:` it is enough to control the length of the recursion:
  if $\\eta\\le \\frac{\\log_2 n}{2(a+c_1+1)\\log_2\\log_2 n}$, then
  $n_\\eta\\ge n^{1/2}$ and the threshold $t'(\\eta)\\le n_\\eta/16$ remains feasible
  (for fixed $a,c_1$ and $n$ sufficiently large).
- `Toy‑check:` for $n=2^{24}$ and $a+c_1\\le 6$ we get
  $n_2\\ge 2^{24}/24^{12}$, that is, the decline in two steps is only polylog-factorial.
- `Attempt to "kill":` if $t'(m)$ grows faster than polylog (for example $2^{\\sqrt{\\log_2 m}}$),
  then the denominator becomes subexponential and $n_\\eta$ falls too quickly.
- `Status:` reduction (explicit formula for the lower bound $n_\\eta$).
- `StepID:` Q43.S205-flat-eval-hr-neta-recursion.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure parametric recursion).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` go to explicit estimate $n_\\eta\\ge n/\\log_2^{O(\\eta)} n$
  in Lean form and fix the range $\\eta$ for HR parameters.

-/

/-!
### 16.346. Research step (reduction): $\\eta$ range for HR parameters

- `Lens:` Invariant.
- `Statement (Q43.S206-flat-eval-hr-neta-range):`
  Let $t'(m)\\le(\\log_2 m)^a$ and
  $n_\\eta\\ge n/(A\\,\\log_2^{a+c_1} n)^\\eta$ (see Section 16.345). Then the choice
  $$\\eta\\le \\frac{\\log_2 n}{2(a+c_1+1)\\log_2\\log_2 n}$$
  guarantees $n_\\eta\\ge n^{1/2}$ and, therefore, for $n$ sufficiently large
  HR thresholds $t'(\\eta)\\le n_\\eta/16$ and $s(\\eta)\\le n_\\eta/32$ are met.
- `Reduction:` the range of $\\eta$ is reduced to the logarithmic number of levels;
  HR checks can withstand such a horizon with fixed $a,c_1$ and base-2 logarithms.
- `Toy‑check:` for $n=2^{24}$, $a+c_1\\le 6$ we get
  $\\eta\\le 24/(14\\log_2 24)\\approx 0.5$, that is, already $\\eta\\le 1$
  provides $n_\\eta\\ge n^{1/2}$.
- `Attempt to "kill":` if $a$ or $c_1$ increases with $n$ (unfixed polylogdegree),
  then the range $\\eta$ can collapse to 0; means fixed parameters
  critical.
- `Status:` reduction (explicit $\\eta$ range for HR parameters).
- `StepID:` Q43.S206-flat-eval-hr-neta-range.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (parametric assessment).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` associate the resulting range $\\eta$ with a real number
  levels in Proof Thm. 4.3 (HR'22) and check that the recursion does not exit
  beyond this horizon at $s,t'\\!=\\mathrm{polylog}(n)$ (base $\\log_2$).

-/

/-!
### 16.347. Exploratory step (reduction): number of levels = depth $d$

- `Lens:` Equivalence.
- `Statement (Q43.S207-flat-eval-hr-level-count):`
  HR'22 (Section 3.4) explicitly builds a **sequence** of complete restrictions
  $\\sigma_1,\\dots,\\sigma_d$ for Frege-proof of depth $d$, and that's it
  $t(k)$evaluations are determined by induction on $k=1,\\dots,d$. Hence,
  the number of levels in the HR construction is $d$.
- `Reduction:` to check the range of $\\eta$ it is enough to control the depth
  $d$ in Thm mode. 4.3 and ensure that $d$ falls within the valid range
  $\\eta\\le \\frac{\\log_2 n}{2(a+c_1+1)\\log_2\\log_2 n}$ (see Section 16.346).
- `Exact citation:`
  HR’22 Section 3.4: “Consider a Frege proof of depth d … We intend to construct a sequence
  of full restrictions $\\sigma_1,\\sigma_2,\\dots,\\sigma_d$ … From the sequence of restrictions we
  require that all sub‑formulas occurring in the proof of depth at most k have functionally
  equivalent $t(k)$‑evaluations … We construct these $t(k)$‑evaluations by induction on k.”
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:798–823`).
- `Toy‑check:` for $d=1$ we have one restriction and one $t(1)$evaluation, which
  consistent with "1 level = depth 1".
- `Status:` reduction (HR levels = depth $d$).
- `StepID:` Q43.S207-flat-eval-hr-level-count.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (citation + parametric link).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` compare the depth $d$ of the Thm mode. 4.3 with $\\eta$ range
  from Section 16.346 and verify that $d$ does not exceed the permissible horizon.

-/

/-!
### 16.348. Exploratory step (reduction): depth $d$ vs range $\\eta$

- `Lens:` Equivalence.
- `Statement (Q43.S208-flat-eval-hr-depth-range):`
  In Thm mode. 4.3 compares the depth $d$ with the range $\\eta$ from Section 16.346.
  Since the number of levels is equal to $d$ (see Section 16.347), the condition
  $$d\\le \\frac{\\log_2 n}{2(a+c_1+1)\\log_2\\log_2 n}$$
  equivalent to requirement
  $$\\kappa\\le \\frac{1}{2(a+c_1+1)}\\qquad\\text{at }\\ d=\\kappa\\,\\frac{\\log_2 n}{\\log_2\\log_2 n}.$$
- `Reduction:` checking the range $\\eta$ comes down to comparing the coefficient $\\kappa$
  with an explicit constant $1/(2(a+c_1+1))$ from HR recursion.
- `Toy‑check:` for $a+c_1\\le 6$ we get $\\kappa\\le 1/14$; if the depth is taken
  with $\\kappa\\ge 1$, the condition is not satisfied.
- `Attempt to "kill":` without explicit constants $a,c_1$ it is impossible to decide whether
  depth mode $d$ from Thm. 4.3 into the allowed range $\\eta$.
- `Status:` reduction (the range $\\eta$ is rewritten through the coefficient $\\kappa$).
- `StepID:` Q43.S208-flat-eval-hr-depth-range.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (parametric assessment).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract/evaluate explicit $a,c_1$ from HR proof
  (Lemma 4.2/6.9) and check whether the $\\kappa$ mode is compatible with the resulting bound.

-/

/-!
### 16.349. Exploratory step (barrier): constants $a,c_1$ in HR are not extracted

- `Lens:` Equivalence.
- `Statement (Q43.S209-flat-eval-hr-depth-range-constants):`
  To compare $\\kappa$ with $1/(2(a+c_1+1))$ we need explicit constants from the HR switching
  lemm. In the HR text these constants are specified as **existing** (without numerical values),
  which makes an explicit comparison inaccessible without a complete restatement of the proof.
- `Exact citation:`
  Lemma 4.2 (Switching Lemma) introduces **absolute** constants $A,C,n_0$ without numbers:
  “There are absolute constants A, C, n0 > 0 …” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1542–1547`).
  Lemma 6.9 also introduces an existence constant:
  “There is a constant A > 0 …” (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1960–1966`).
  In the proof of Lemma 4.2 "appropriate constants $A_0,A_1,A_2$" appear
  without values (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:1987–1996`),
  and in the proof of Lemma 6.9 - the constants $A_1,A_2,A_3,A_4$ "for some constant"
  (`resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:2336–2351`).
- `Barrier certificate:` without explicit $A,C,n_0$ and constants from Lemma 6.9 it is impossible to calculate
  numerical $a,c_1$ at threshold $\\eta$; the $\\kappa$ comparison remains unfixed.
- `Status:` barrier (constants are implicit).
- `StepID:` Q43.S209-flat-eval-hr-depth-range-constants.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure parametric connection).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` recalculate Lemma 6.9/4.2 with explicit numbers or fix
  range $\\kappa$ via external explicit constants (if possible).

-/

/-!
### 16.350. Exploratory step (proof): explicit upper bounds for $A_3,A_4$

- `Lens:` Equivalence.
- `Statement (Q43.S210-flat-eval-hr-depth-range-constants-recount):`
  The proof of Lemma 6.9 uses the estimates
  $$s+16t+s/4\\le A_3 s\\qquad\\text{and}\\qquad |S_g^*|\\le s/4+16t\\le A_4 s,$$
  where $t\\le s$. From here we can fix explicit integer constants
  $$A_3\\le 18,\\qquad A_4\\le 17.$$
- `Proof:` the inequalities have been formally proven in Lean
  $s+16t+s/4\\le 18s$ and $s/4+16t\\le 17s$ at $t\\le s$
  (see `formal/WIP/Work.lean`, Q43_Lemma69_A3_bound, Q43_Lemma69_A4_bound).
- `Status:` proof (explicit upper bounds for $A_3,A_4$).
- `StepID:` Q43.S210-flat-eval-hr-depth-range-constants-recount.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure parameter arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract explicit $A_1,A_2$ (and then $A_0$) from Lemma 6.9/4.2.

-/

/-!
### 16.351. Exploratory step (proof): reduction to explicit $A_1,A_2$

- `Lens:` Equivalence.
- `Statement (Q43.S211-flat-eval-hr-depth-range-constants-a1a2):`
  Let $t\\le s$ be satisfied in Lemma 6.9 and there be constants $A_1,A_2$ in terms
  additional volume information. Then the total contribution of blocks of size $|S_g^*|$ and tail
  $s+16t+s/4$ is limited by the formula
  $$9|S_g^*| + A_1|S_g^*| + A_2|S_g^*| + (s+16t+s/4)
    \\le (9+A_1+A_2)\\cdot 17s + 18s.$$
- `Proof:` The above estimate is formally proven in Lean (see. `formal/WIP/Work.lean`,
  Q43_Lemma69_A12_bound), using explicit upper bounds $A_3\\le 18$ and $A_4\\le 17$.
- `Status:` proof (reducing the total $A$ to $A_1,A_2$).
- `StepID:` Q43.S211-flat-eval-hr-depth-range-constants-a1a2.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure parameter arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract explicit $A_1,A_2$ and then $A_0$ from Lemma 6.9/4.2.

-/

/-!
### 16.352. Exploratory step (proof): explicit aggregation of $A_0$factor

- `Lens:` Equivalence.
- `Statement (Q43.S212-flat-eval-hr-depth-range-constants-a0):`
  The log factor $A_0\\log n'$ is multiplied by $\\Delta^{a+b}$, and the product
  $\\Delta^a\\cdot\\Delta^b$ can be collapsed into $\\Delta^{a+b}$:
  $$(A_0\\log n')\\,\\Delta^a\\,\\Delta^b=(A_0\\log n')\\,\\Delta^{a+b}.$$
- `Proof:` the formal lemma in Lean uses $\\Delta^{a+b}=\\Delta^a\\cdot\\Delta^b$
  (see `formal/WIP/Work.lean`, Q43_Lemma69_A0_bound).
- `Status:` proof (aggregation of $A_0$ factor).
- `StepID:` Q43.S212-flat-eval-hr-depth-range-constants-a0.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: yes (pure arithmetic).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` extract the explicit value of $A_0$ from Lemma 5.5/4.2.

-/

/-!
### 16.314. Research step (reduction): sweep exp->$2^{(\\cdot)}$ in Q43

- `Lens:` Compression/canonization.
- `Statement (Q43.S174-exp2-threshold-sweep):`
  All Q43 estimates of exponential growth use the form $2^{(\\cdot)}$
  (according to $\\log_2$ from HR'22); for Chernov tails and estimates,
  where the natural base is explicitly used, $e^{(\\cdot)}$ is written.
  Remaining mentions `exp` - only in direct quotes from sources.
- `Toy test:` $2^{(\\log n)^k}$ is superpolynomial for $k>1$; For example
  $2^{(\\log_2 n)^2}=n^{\\log_2 n}$ exceeds $n^c$ for any fixed $c$.
- `Exact citation:`
  base of logarithms $\\log_2$ in HR'22 -- `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:271`.
- `Status:` reduction (normalization of notation).
- `StepID:` Q43.S174-exp2-threshold-sweep.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (notation).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` go through Q43 citations and add short notes "exp in source = 2^x"
  where this affects the interpretation of thresholds.

-/

/-!
### 16.310. Research step (reduction): explicit $c_1,c_2$ in Proof Thm. 4.1

- `Lens:` Equivalence.
- `Statement (Q43.S170-explicit-c1c2-thm41):`
  We take the explicit constants from Section 16.302-Section 16.303 and Section 16.215:
  $A_1^{\\mathrm{tot}}=24$, $A_2\\le 16$, $A_3,A_4\\le 18$ (rough integer
  rounding $69/4$), so you can take
  $$A_{\\mathrm{bits}}:=24+16+18+18=76,\\qquad A:=2^{76}.$$
  Here the base $2$ corresponds to the binary bit count; for $\\log=\\ln$ can be replaced
  $2^{76}$ by $e^{76\\ln 2}$ (equivalent constant).
  Then in Proof Lemma 4.2 we can fix the constant
  $$c_2:=8\\cdot 152\\cdot A,$$
  taking into account the rounding of $\\lfloor\\cdot\\rfloor$, and in Proof Thm. 4.1 set
  $$c_1:=16\\cdot 152\\cdot c_2.$$
  With these $c_1,c_2$ the formula $\\log N\\le n^{1/d}/(c_1\\log^4 n)$ guarantees
  $t_d=152\\log N\\le n_d/16$, and recursion
  $n_i=\\lfloor n_{i-1}/(4A t_{i-1}\\log^4 n_{i-1})\\rfloor$ gives
  $n_d\\ge n/(\\log^{d-1} N\\cdot(c_2\\log^4 n)^d)$ (rough but explicit estimate).
- `Toy test:` for $d=1$ we have
  $n_1\\ge n/(8A t\\log^4 n)$ for $n\\ge 2$; then with $t=152\\log N$
  and $c_1=16\\cdot 152\\cdot c_2$ we get $t_1\\le n_1/16$.
- `Exact citation:`
  Proof Thm parameters. 4.1 and inequality (5) -
  `resources/text_cache/hastad_risse_2022_tseitin_grid_revisited.txt:889–931`.
- `Status:` reduction (explicit $c_1,c_2$ are specified; hidden constants are eliminated).
- `StepID:` Q43.S170-explicit-c1c2-thm41.
- `InfoGain:` 1.
- `Barrier check (A/B/C):`
  A) Relativization check: relativized (arithmetic of constants).
  B) Natural proofs check: not applicable.
  C) Algebrization check: not applicable.
- `Next step:` check the interpretation of the threshold $M>e^{n^\\alpha}$ with these
  explicit constants and agree on the logarithm base throughout Q43.

-/
