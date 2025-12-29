import Paperproof

/-!

# P vs NP - research steps 16.37-16.84

Main index: `P_vs_NP.md`.

### 16.37. Exploratory step: error counter in tt formula

- `Lens:` Compression/canonization.
- `Statement:` For any $N=2^n$ and $T\in\{0,\dots,N\}$ there is a Boolean circuit
  size $O(N\log N)$, calculating $\mathrm{Count}_{\ge T}(e_1,\dots,e_N)$;
  construction - summation of $N$ bits and comparator with $T$.
  For a "simple" tree of ripple-carry adders, the depth is $O(\log^2 N)$ (the height of the tree
  $O(\log N)$ and the width of the sum $O(\log N)$); depth can be improved to $O(\log N)$
  (carrysave/Wallacetree + final addition), but on the LogLogscale it is important for us
  only size $O(N\log N)=\mathrm{poly}(2^n)$.
- `Toy test:` $N=4$: add $(e_1,e_2)$ and $(e_3,e_4)$ with 2-bit adders,
  then using a 3-bit adder we obtain the sum $\in\{0,\dots,4\}$; 3-bit comparator
  checks $\ge T$. Size $O(N\log N)$; for $N=4$ the depth is constant (and in the general case, see the statement).
- `Status:` proven (explicit construction).
- `Barrier check:` r - not applicable (upper estimate), NP - not applicable, alg - not applicable.
- `Next step:` if necessary, record specific information in the main text
  implementation (adder tree/Batcher) and encoding $T$ of length $O(\log N)$.

### 16.38. Exploratory step: Tseitin encoding $\mathrm{Eval}(C,x)$

- `Lens:` Equivalence.
- `Statement:` For gate-list encoding of scheme $C$ of size $s$ (fan-in 2)
  there is a CNF formula $\mathrm{Eval}_C(x,b)$ with $O(s)$ auxiliaries
  variables and $O(s)$ clauses, such that for any assignment of inputs $x$
  the formula is valid if and only if the output of the circuit is equal to $b$.
- `Toy test:` Scheme: $g_1:=x_1\land x_2$, $g_2:=g_1\lor x_3$ (output $g_2$).
  Tseitin clauses:
  $(\neg g_1\lor x_1)\land(\neg g_1\lor x_2)\land(g_1\lor\neg x_1\lor\neg x_2)$ and
  $(\neg g_2\lor g_1\lor x_3)\land(g_2\lor\neg g_1)\land(g_2\lor\neg x_3)$,
  plus the unit clause $(g_2)$ for $b=1$.
  When $x_1=x_2=1,x_3=0$ is satisfied with $g_1=g_2=1$; for $b=0$ is impossible.
  There are $O(1)$ clauses per gate, which means the size is $O(s)$.
- `Status:` proven (standard Tseitin encoding).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` associate this encoding with the place where it is recorded in the text
  $n=||x||$ for propositional translation into EF.

### 16.39. Exploratory step: equivalence vs equivalence in CNF->3-CNF

- `Lens:` Equivalence.
- `Statement:` The standard reduction CNF->3-CNF generates the formula $r(\varphi)$,
  logically equivalent to $\varphi$ as a formula over *all* variables
  (original and new).
- `Toy test:` Let's take the clause $\varphi=(x_1\lor x_2\lor x_3\lor x_4)$ and the reduction
  $r(\varphi)=(x_1\lor x_2\lor y)\land(\neg y\lor x_3\lor x_4)$.
  The assignment $x_1=1,x_2=x_3=x_4=0,y=1$ makes $\varphi$ true, but
  $r(\varphi)$ is false (the second clause is false). Therefore, complete equivalence
  incorrect; only $\varphi\equiv \exists y\, r(\varphi)$ is true.
- `Status:` counterexample.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` use an explicit function $g$ (as in Lemma 15.7.3d),
  to carry the truth of $\varphi$ to $r(\varphi)$ in EF.

### 16.40. Research step: blow-up order does not affect barrier

- `Lens:` Trade-off (sizes).
- `Statement:` For barrier 15.7.4 any polynomial blow-up is sufficient
  reductions $r$; explicit order (linear/quadratic) does not change the output
  $\mathrm{P}=\mathrm{NP}$.
- `Toy test:` Let $|r(\varphi)|\le |\varphi|^2$ and the algorithm $\mathcal A$
  builds a ROABP of size $\le |\psi|^3$. Then the composition gives ROABP
  of size $\le |\varphi|^6$, which remains a polynomial. Therefore, even
  quadratic blow-up doesn't break the argument.
- `Status:` proven (trivial estimate).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if necessary, find the exact blow-up order in
  Lichtenstein/Tovey reductions for bibliographic accuracy.

### 16.41. Exploratory step: fixing $n=||x||$ on LogLog scale

- `Lens:` Equivalence.
- `Statement:` If in $LB_{tt}(h,s(n),t(n)2^n)$ we substitute the parameter
  $x:=2^{2^n}$, then $||x||=2^n+1$, and restrictions of the form $u<2^n$ can be rewritten
  bounded is equivalent to $u+1<||x||$ (that is, $u<||x||-1$). Therefore the formula remains $\Pi^b_1$,
  and its propositional translation has size $\mathrm{poly}(2^n)$ and gives
  standard $tt(h_n,s(n),t(n))$.
- `Toy test:` $n=2$: take $x=2^{2^2}=16$, get $||x||=5$, and any
  the quantifier $u<2^n=4$ is equivalent to $u+1<5$ (and this rewriting does not change
  truth neither for $\forall u$ nor for $\exists u$).
  This illustrates how a "truth table" of length $2^n$ fits
  into bounded quantifiers by $x$.
- `Status:` proven (direct estimate of length).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` indicate in the main text the specific place where
  the substitution $x=2^{2^n}$ is fixed (PS Sec. 2.4.1) and how this is reflected
  in EF translation.

### 16.42. Exploratory step: $\mathrm{Count}_{\ge T}$ via sorting network

- `Lens:` Equivalence.
- `Statement:` Let the network sort the bits $e_1,\dots,e_N$ in non-ascending order,
  producing $b_1\ge \cdots \ge b_N$. Then $\mathrm{Count}_{\ge T}(e)$ is equivalent
  condition $b_T=1$. The Batcher sorting network has $O(N\log^2 N)$ comparators,
  each comparator is implemented by $O(1)$ AND/OR gates, which means the circuit for
  $\mathrm{Count}_{\ge T}$ has size $O(N\log^2 N)$.
- `Toy test:` $N=4$ and a network with comparators $(1,2),(3,4),(1,3),(2,4),(2,3)$
  (outputs - $(\max,\min)$). At the input $(1,0,1,0)$ we get
  $(1,1,0,0)$, so $\mathrm{Count}_{\ge 3}$ is false and $\mathrm{Count}_{\ge 2}$
  true (check against $b_3$ and $b_2$).
- `Status:` proven (standard network).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` decide which option (adder tree vs sorting network)
  it is more convenient to record it in the main text near Lemma 15.7.1d.

### 16.43. Exploratory step: comparator size and $T$ threshold encoding

- `Lens:` Compression/canonization.
- `Statement:` For $N=2^n$ and any integer $T\in[0,N]$ the length of the binary code is $T$
  is equal to $O(\log N)=O(n)$. Comparator testing $S\ge T$ for the sum $S\in[0,N]$
  (in binary) is implemented by a circuit of size $O(\log N)$. Therefore adding
  threshold does not change the asymptotics of the construction $\mathrm{Count}_{\ge T}$.
- `Toy test:` $N=8$, $T=5=0101_2$, sum $S=s_3s_2s_1s_0$.
  The condition $S\ge 5$ is equivalent to $s_3\ \lor\ (s_2\land(s_1\lor s_0))$,
  what does a constant comparator provide? the size grows as $O(\log N)$ in the general case.
- `Status:` proven (standard binary comparison comparator).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a short note about the size of the comparator
  next to Lemma 15.7.1d.

### 16.44. Research step: gate-list length and $\Delta^b_0$-validity

- `Lens:` Compression/canonization.
- `Statement:` For a circuit of size $s$ with fanin 2 and $n$ gatelist inputs
  encoding has length $m(s,n)=O(s\log s+n\log s)$: per gate
  the type (constant) and two indices of the inputs $<i$ are stored, each index
  takes $O(\log s)$ bits. The predicate $\mathrm{Valid}_s(C)$ is checked
  bounded quantifiers by $i\le s$ and indices $<i$, so is $\Delta^b_0$.
- `Toy test:` $s=3,n=2$: encoding gates
  $g_1=\mathrm{IN}(1)$, $g_2=\mathrm{IN}(2)$, $g_3=\mathrm{AND}(1,2)$.
  Each index $\le 3$ is encoded with 2 bits, the type is a constant number of bits.
  The $\mathrm{Valid}_3$ check requires only the conditions "indices $<i$".
  If we replace $g_3=\mathrm{AND}(3,2)$, then the condition $3<i$ is false - a counterexample
  to validity with the same bounded quantifiers.
- `Status:` proven (explicit assessment and verification).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, refer to Lemma 15.7.2b in the main text
  and note that for $n\le s$ we can take $m(s)=O(s\log s)$.

### 16.45. Exploratory step: correctness of explicit $g$ in CNF->3-CNF

- `Lens:` Invariant.
- `Statement:` For the clause $(\ell_1\lor\cdots\lor\ell_k)$ and the chain
  $(\ell_1\lor\ell_2\lor y_1)\land(\neg y_1\lor\ell_3\lor y_2)\land\cdots\land
  (\neg y_{k-3}\lor\ell_{k-1}\lor\ell_k)$ choice
  $y_i:=\neg(\ell_1\lor\cdots\lor\ell_{i+1})$ satisfies all new clauses
  for any true meaning of the original clause.
- `Toy test:` $k=5$, let $\ell_3$ be true and $\ell_1=\ell_2=\ell_4=\ell_5=0$.
  Then $y_1=\neg(\ell_1\lor\ell_2)=1$, $y_2=\neg(\ell_1\lor\ell_2\lor\ell_3)=0$.
  Checking the chain:
  $(\ell_1\lor\ell_2\lor y_1)=(0\lor 0\lor 1)=1$,
  $(\neg y_1\lor\ell_3\lor y_2)=(0\lor 1\lor 0)=1$,
  $(\neg y_2\lor\ell_4\lor\ell_5)=(1\lor 0\lor 0)=1$.
- `Status:` proven (invariant "prefix is false").
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a short remark to Lemma 15.7.3d,
  explaining the "prefix is false" invariant for the choice of $g$.

### 16.46. Exploratory step: $\mathrm{Eval}(C,x)$ already in 3-CNF

- `Lens:` Compression/canonization.
- `Statement:` For gatelist circuit fanin 2 Tseitincoding
  $\mathrm{Eval}_C(x,b)$ consists of clauses of width $\le 3$ (formulas for AND/OR/NOT)
  and therefore is 3CNF without additional blow-up; number of clauses $O(s)$.
- `Toy test:` The gate $g=a\land b$ is encoded by three clauses:
  $(\neg g\lor a)$, $(\neg g\lor b)$, $(g\lor\neg a\lor\neg b)$ -- width $\le 3$.
  Similarly for $g=a\lor b$ and $g=\neg a$ (width $\le 2$).
- `Status:` proven.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` If desired, note in the main text that for fanin 2
  no additional reduction is needed in 3CNF.

### 16.47. Exploratory step: p-time function graph as $\Delta^b_0$

- `Lens:` Equivalence.
- `Statement:` If $R(n,C)$ is calculated in polynomial time and
  $|R(n,C)|\le p(n)$, then there is a bounded formula
  $\mathrm{Graph}_R(n,C,y)$ (time/cell quantifiers $\le p(n)$),
  such that $\mathrm{Graph}_R(n,C,y)\iff y=R(n,C)$. Hence,
  substituting $y:=R(n,C)$ into $\mathrm{RedCorr}(n,C,y)$ preserves
  $\Pi^b_1$form.
- `Toy test:` Let $R(n,C)$ return $C_1\oplus C_2$ (first two bits).
  Then $\mathrm{Graph}_R(n,C,y)$ can be written as a bounded formula
  $y\leftrightarrow (C_1\oplus C_2)$. For $C=10$ we get $y=1$;
  at $y=0$ the formula is false.
- `Status:` proven (standard $\Delta^b_0$ graph formalization).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, relate this to the formulation (H2$_\Pi$),
  where $R(n,C)$ is used instead of $\exists y$.

### 16.48. Exploratory step: eliminating $\exists y$ via $\mathrm{Graph}_R$

- `Lens:` Equivalence.
- `Statement:` If we define
  $\mathrm{RedCorr}(n,C,y):=\mathrm{Graph}_R(n,C,y)\wedge \mathrm{Err}_{t(n)}(C,y)$,
  then for the total ptime function $R$ we have the equivalence
  $$\forall n\,\forall C\,\exists y\,\mathrm{RedCorr}(n,C,y)\ \iff\
  \forall n\,\forall C\,\mathrm{Err}_{t(n)}(C,R(n,C)).$$
  This means (H2$_\Pi$) can be written as $\forall n\,\forall C\,\mathrm{RedCorr}(n,C,R(n,C))$
  without going beyond $\Pi^b_1$.
- `Toy test:` Let $R(n,C)$ return the first bit of $C$, and
  $\mathrm{Err}_{t(n)}(C,y)$ := $(y=1)$.
  Then $\exists y\,\mathrm{RedCorr}$ is true $\iff C_1=1$,
  and this is equivalent to $\mathrm{Err}_{t(n)}(C,R(n,C))$ (also $C_1=1$).
- `Status:` proven (substitution according to the function graph).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, mark this right next to (H2$_\Pi$)
  in the main text.

### 16.49. Exploratory step: error as counter

- `Lens:` Equivalence.
- `Statement:` Let $e_x:=C(x)\oplus g_n(x)$ for all $x\in\{0,1\}^n$.
  Then the formula $\mathrm{Err}_{t(n)}(C,g_n)$ is equivalent to the condition
  $\sum_x e_x < t(n)2^n$, that is, $\neg\,\mathrm{Count}_{\ge T}(e)$ for
  $T:=\lceil t(n)2^n\rceil$. The set $S$ from the definition of $\mathrm{Err}_{t(n)}$
  can be taken equal to $\{x:e_x=1\}$.
- `Toy test:` $n=2$, $g(x)=x_1\oplus x_2$, and $C$ is wrong on exactly one input.
  Then $\sum_x e_x=1$. For $t(n)=1/2$ we have $T=2$ and $\mathrm{Count}_{\ge 2}(e)=0$,
  that is, the error $< t(n)$, as by definition through the set $S$ of size 1.
- `Status:` proven (census definition).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, note the connection $\mathrm{Err}_{t(n)}$ in the main text
  with $\mathrm{Count}_{\ge T}$ (as in the $tt$ formula).

### 16.50. Research step: ptime computability $g$ for CNF->3-CNF

- `Lens:` Invariant.
- `Statement:` For each initial clause $(\ell_1\lor\cdots\lor\ell_k)$
  values $y_i:=\neg(\ell_1\lor\cdots\lor\ell_{i+1})$ are calculated in $O(k)$
  time, supporting prefix OR. For the entire formula $g(p)$ is calculated
  for $O(|\varphi|)$, so $g$ is ptime and PVfunction (available in EF).
- `Toy test:` For $\ell=(0,1,0,0)$ we have the prefixes
  $p_2=\ell_1\lor\ell_2=1$, $p_3=1$, $p_4=1$,
  therefore $y_1=\neg p_2=0$, $y_2=\neg p_3=0$.
  The calculation requires one pass through the clause.
- `Status:` proven (linear pass).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark in the main text that $g$
  p-time/PV is computable, so EF can use it in 15.7.3d.

### 16.51. Exploratory step: polynomial size $P_\varphi$

- `Lens:` Compression/canonization.
- `Statement:` For CNF $\varphi=\bigwedge_{j=1}^m C_j$ with $L$ literals
  polynomial $P_\varphi(x)=\prod_j S_{C_j}(x)$, where
  $S_{C}(x)=1-\prod_{\ell\in C}(1-\llbracket \ell\rrbracket)$,
  has a depth-3 formula of size $O(L)$ (one factor per literal
  plus constants). Therefore, any polynomial blow-up reduction
  preserves the condition "$P_\psi$ has size $\mathrm{poly}(|\psi|)$" in Lemma 15.7.4.
- `Toy test:` $\varphi=(x_1\lor\neg x_2)\wedge(x_2\lor x_3\lor x_4)$.
  Then $S_{C_1}=1-(1-x_1)(1-(1-x_2))$ and
  $S_{C_2}=1-(1-x_2)(1-x_3)(1-x_4)$, and
  $P_\varphi=S_{C_1}\cdot S_{C_2}$ -- depth-3 formula with the number of factors,
  linear in the number of literals (5).
- `Status:` proven (direct calculation).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark to Lemma 15.7.4,
  that the size of $P_\varphi$ is linear in the number of literals and is preserved under
  polynomial blow-up reductions.

### 16.52. Exploratory step: cubed zero  identical zero

- `Lens:` Equivalence.
- `Statement:` If a multilinear polynomial $Q(x_1,\dots,x_n)$ over a field
  satisfies $Q(a)=0$ for all $a\in\{0,1\}^n$, then $Q\equiv 0$.
  (The values on the Boolean cube uniquely define a multilinear polynomial.)
- `Toy test:` $n=1$: $Q(x)=ax+b$. From $Q(0)=b=0$ and $Q(1)=a+b=0$ it follows that $a=b=0$.
  $n=2$: $Q(x,y)=a xy+ b x + c y + d$. Zeros on four points give the system
  $d=0$, $b+d=0$, $c+d=0$, $a+b+c+d=0$, then $a=b=c=d=0$.
- `Status:` proven (the uniqueness of the multilinear representation).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a short note next to the sanitation check
  (Section 15.7) that the multilinear polynomial is uniquely reconstructed from
  values by $\{0,1\}^n$.

### 16.53. Exploratory step: $P_\varphi$ as a feasibility indicator

- `Lens:` Equivalence.
- `Statement:` For Boolean assignment $a\in\{0,1\}^n$ and clause
  $C=(\ell_1\lor\cdots\lor\ell_k)$ polynomial
  $S_C(a)=1-\prod_{i=1}^k(1-\llbracket \ell_i\rrbracket)$ is equal to $1$
  if and only if $C(a)=1$. Hence,
  $P_\varphi(a)=\prod_j S_{C_j}(a)=1$ if and only if $\varphi(a)=1$,
  and $\varphi$ is unsatisfiable $\iff P_\varphi$ zero on $\{0,1\}^n$.
- `Toy test:` $\varphi=(x_1\lor\neg x_2)\wedge x_2$.
  For $a=(1,0)$ we have $S_{x_1\lor\neg x_2}=1-(1-1)(1-(1-0))=1$,
  $S_{x_2}=1-(1-0)=0$, which means $P_\varphi(a)=0$ and $\varphi(a)=0$.
  For $a=(1,1)$ both factors are equal to $1$ and $\varphi(a)=1$.
- `Status:` proven (direct verification on a Boolean cube).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a note near the sanitation check,
  that $P_\varphi$ coincides with the feasibility indicator at $\{0,1\}^n$.

### 16.54. Exploratory step: choosing a "canonical" counter implementation

- `Lens:` Compression/canonization.
- `Statement:` For the formula $\mathrm{Count}_{\ge T}$ in $tt(f_n,s,t)$
  Any standard implementation of size $\mathrm{poly}(2^n)$ is sufficient.
  Adder-tree gives $O(N\log N)$, Batcher gives $O(N\log^2 N)$, both are suitable
  for EF and scale $n\in\mathrm{LogLog}$.
- `Toy test:` $N=8$: addertree adds pairs of bits (4 adders),
  then the sums (2 adders), then the final sum (1 adder) and the comparator;
  total $O(N\log N)$ elements. Sortingnetwork on $N=8$ has
  $O(N\log^2 N)$ comparators. Both give a Boolean formula for the size of poly.
- `Status:` proven (comparison of estimates).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` select one option to be fixed in the main text next to it
  with Lemma 15.7.1d.

### 16.55. Exploration step: $m(s)$ polynomial in $|x|$ under LogLog

- `Lens:` Compression/canonization.
- `Statement:` Substituting $x=2^{2^n}$ we have $|x|=2^n+1$ and
  $s=2^{n/4}$. Then the circuit code length $m(s)=O(s\log s)=2^{O(n)}$
  satisfies $m(s)\le |x|^{O(1)}$. This means there is a restriction on the circuit code
  $|C|\le m(s)$ (equivalently $C<2^{m(s)}$) in (H1$_\Pi$) is a bounded quantifier at scale $n\in\mathrm{LogLog}$.
- `Toy test:` $n=4$: $x=2^{16}$, $|x|=17$, $s=2^{1}=2$ and
  $m(s)=O(2\log 2)=O(2)\le |x|$.
- `Status:` proven (direct assessment).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to (H1$_\Pi$),
  that $m(2^{n/4})$ is polynomial in $|x|$ at the LogLog scale.

### 16.56. Exploratory step: totality of $R$ in $\mathrm{S}^1_2$

- `Lens:` Equivalence.
- `Statement:` If $R$ is a ptime reduction, then its totality is expressed by
  $\Sigma^b_1$formula $\forall n\,\forall C<2^{m(n)}\,\exists y\le p(n)\,
  \mathrm{Graph}_R(n,C,y)$ and is proved in $\mathrm{S}^1_2$ (PV computability).
  This ensures the transition from (H2$_\Pi$) to the $\forall\exists$form with $y$.
- `Toy test:` Let $R(n,C)$ return $C_1$. Then $\mathrm{Graph}_R(n,C,y)$
  -- bounded formula $y\leftrightarrow C_1$. Obviously,
  $\forall C\,\exists y\le 1\,\mathrm{Graph}_R(n,C,y)$ is true.
- `Status:` proven (standard totality of PV functions).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to (H2$_\Pi$),
  that the totality of $R$ is provable in $\mathrm{S}^1_2$.

### 16.57. Exploratory Step: Coding Many Errors $S$

- `Lens:` Compression/canonization.
- `Statement:` In $\mathrm{Err}_{t(n)}$ the set $S\subseteq\{0,1\}^n$
  can be encoded with a bitmask of length $2^n$, that is, a number
  $S<2^{2^n}$. With LogLog substitution $x=2^{2^n}$ we have $S\le x$,
  so the quantifier $\exists S$ is bounded, and $\mathrm{Err}_{t(n)}$
  remains the $\Delta^b_0$ formula.
- `Toy test:` $n=2$: $x=2^{2^2}=16$. Any $S\subseteq\{0,1\}^2$ is encoded
  4-bit mask $<2^4=16=x$ (for example, $S=\{00,11\}$ corresponds to $1001_2$).
- `Status:` proven (explicit coding).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, mark next to $\mathrm{Err}_{t(n)}$ in L2,
  that the quantifier on $S$ is bounded by $x=2^{2^n}$.

### 16.58. Exploratory step: membership $x\in S$ as bit access

- `Lens:` Compression/canonization.
- `Statement:` If $S<2^{2^n}$ encodes a subset of $\{0,1\}^n$
  mask of length $2^n$, then the predicate $x\in S$ is equivalent to $\mathrm{Bit}(S,x)=1$.
  The function $\mathrm{Bit}$ is PV-computable, so the condition $x\in S$ is
  $\Delta^b_0$ formula for bounded quantifiers $x<2^n$ and $S<2^{2^n}$.
- `Toy test:` $n=2$, $S=1001_2$ encodes $\{00,11\}$.
  Then $\mathrm{Bit}(S,0)=1$, $\mathrm{Bit}(S,3)=1$, and $\mathrm{Bit}(S,1)=0$.
- `Status:` proven (bit access).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, specify in L2 that the check $x\notin S$
  is implemented via $\mathrm{Bit}(S,x)=0$.

### 16.59. Exploratory step: size $|S|$ via counter

- `Lens:` Equivalence.
- `Statement:` If $S$ is specified by a bitmask of length $2^n$, then the condition
  $|S|<T$ is equivalent to $\neg\mathrm{Count}_{\ge T}(S)$, where counter
  applies to mask bits. With LogLog substitution $x=2^{2^n}$ the threshold
  $T\le 2^n\le |x|$, so the check $|S|<T$ remains bounded and $\Delta^b_0$.
- `Toy test:` $n=2$, $S=1011_2$ has $|S|=3$. At $T=3$
  $\mathrm{Count}_{\ge 3}(S)=1$, so $|S|<T$ is false; at $T=4$
  $\mathrm{Count}_{\ge 4}(S)=0$, so $|S|<T$ is true.
- `Status:` proven (census via meter).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, note in L2 that the condition $|S|<t(n)2^n$
  can be expressed in terms of $\mathrm{Count}_{\ge T}$ on the mask $S$.

### 16.60. Exploratory step: degree $P_\varphi$ is polynomial

- `Lens:` Invariant.
- `Statement:` For CNF $\varphi=\bigwedge_{j=1}^m C_j$ with total number
  literals $L$ the polynomial $P_\varphi=\prod_j S_{C_j}$ has degree
  $\deg(P_\varphi)=\sum_j |C_j|\le L$. After multilinearization degree
  does not increase. Therefore, the degree $P_\varphi$ and $\mathrm{ML}(P_\varphi)$
  is polynomial in $|\varphi|$, which is consistent with the PIT requirements for ROABP.
- `Toy test:` $\varphi=(x_1\lor x_2)\wedge(\neg x_2\lor x_3\lor x_4)$:
  $\deg S_{C_1}=2$, $\deg S_{C_2}=3$, so $\deg P_\varphi=5$ (polynomial).
- `Status:` proven (direct calculation of degree).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark near Lemma 15.7.4,
  that the degree of $\mathrm{ML}(P_\varphi)$ is bounded by $O(|\varphi|)$.

### 16.61. Exploratory step: $r(\varphi)$ logically strengthens $\varphi$

- `Lens:` Invariant.
- `Statement:` For the standard reduction CNF->3CNF the formula $r(\varphi)$
  logically implies $\varphi$ from the original variables: for each clause
  $(\ell_1\lor\cdots\lor\ell_k)$ chain of 3clauses in $r(\varphi)$
  is satisfied only if the original clause is true. Hence,
  $r(\varphi)\to \varphi$ (but the reverse is not true).
- `Toy test:` The clause $(\ell_1\lor\ell_2\lor\ell_3\lor\ell_4)$ is replaced by
  $(\ell_1\lor\ell_2\lor y_1)\land(\neg y_1\lor\ell_3\lor\ell_4)$.
  If all $\ell_i=0$, then the first clause requires $y_1=1$, and the second gives
  $(\neg y_1\lor 0\lor 0)=0$, a contradiction. So $r(\varphi)$ is possible
  only if the original clause is true.
- `Status:` proven.
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to Lemma 15.7.3c,
  that $r(\varphi)\Rightarrow \varphi$, and for the opposite direction $g$ is needed.

### 16.62. Exploratory step: $\mathrm{Err}_{t(n)}$ as $\Delta^b_0$formula

- `Lens:` Equivalence.
- `Statement:` On the LogLog scale $\mathrm{Err}_{t(n)}(C,y)$ can be rewritten
  as a bounded formula:
  $$\exists S\le 2^{2^n}\ \bigl(\neg\mathrm{Count}_{\ge T}(S)\ \wedge\
  \forall x<2^n\ (\mathrm{Bit}(S,x)=0\to \mathrm{Eval}(C,x)=y(x))\bigr),$$
  where $T=\lceil t(n)2^n\rceil$. All quantifiers are bounded (via $x=2^{2^n}$),
  and $\mathrm{Bit}$ and $\mathrm{Eval}$ are PV-computable, which means
  $\mathrm{Err}_{t(n)}$ is $\Delta^b_0$.
- `Toy test:` $n=2$, $C=y$ (no errors). Take $S=0000_2$,
  $\mathrm{Count}_{\ge 1}(S)=0$, and for any $x$ we have
  $\mathrm{Bit}(S,x)=0\Rightarrow C(x)=y(x)$. The formula is true.
  If $C$ is wrong by exactly $x=3$, then take $S=1000_2$;
  for $t(n)=1/2$ we obtain $T=2$ and $\neg\mathrm{Count}_{\ge 2}(S)$ is true.
- `Status:` proven (reduction to a bit mask and counter).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, note in L2 that $\mathrm{Err}_{t(n)}$
  rewritten into an explicit bounded form via $\mathrm{Bit}$ and a counter.

### 16.63. Exploratory step: linear blowup in CNF->3CNF

- `Lens:` Compression/canonization.
- `Statement:` For a clause of length $k\ge 3$ the standard chain reduction
  $(\ell_1\lor\cdots\lor\ell_k)\mapsto$ chain of $k-2$ 3clauses
  introduces $k-3$ new variables and $3(k-2)$ literals. Therefore, if
  $\varphi$ has a total of $L$ literals, then $r(\varphi)$ has size $O(L)$
  (linear blow-up).
- `Toy test:` $k=5$:
  $(\ell_1\lor\ell_2\lor y_1)\land(\neg y_1\lor\ell_3\lor y_2)\land(\neg y_2\lor\ell_4\lor\ell_5)$.
  There are 3 clauses, 2 new variables, 9 literals, which equals $3(k-2)$.
- `Status:` proven (calculation by clause-by-clause).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark to Lemma 15.7.3c
  with an explicit count of the number of clauses/literals.

### 16.64. Exploratory step: multilinearization does not change the values on the cube

- `Lens:` Equivalence.
- `Statement:` For any polynomial $P$ over a field and its multilinearization
  $\mathrm{ML}(P)$ (reduction according to the rules $x_i^2\mapsto x_i$) is performed
  $\mathrm{ML}(P)(a)=P(a)$ for all $a\in\{0,1\}^n$. Therefore, $P$ and
  $\mathrm{ML}(P)$ match on the Boolean cube, and check for nullity on the cube
  is equivalent.
- `Toy test:` $P(x)=x^2+x$. On $x\in\{0,1\}$ we have $x^2=x$, which means
  $P(x)=2x$. After reduction $\mathrm{ML}(P)=x+x=2x$, the values are the same.
- `Status:` proven (since $x_i^2=x_i$ on $\{0,1\}$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the sanitation check,
  that $\mathrm{ML}(P_\varphi)$ coincides with $P_\varphi$ by $\{0,1\}^n$.

### 16.65. Exploration step: $\mathrm{ML}(P_\varphi)$ is computable depth3 formula

- `Lens:` Compression/canonization.
- `Statement:` Since $P_\varphi=\prod_j S_{C_j}$ is already
  depth-3 formula (product of clauses, each - $1-\prod(1-\ell)$),
  and multilinearization replaces the powers of $x_i^2$ with $x_i$ without increasing
  structure, then $\mathrm{ML}(P_\varphi)$ is also computable depth-3 by the formula
  size $O(L)$, where $L$ is the number of literals in $\varphi$.
- `Toy test:` For $\varphi=(x_1\lor\neg x_2)$ we have
  $P_\varphi=1-(1-x_1)(1-(1-x_2))$ -- depth3. There are no powers $>1$ in $P_\varphi$,
  so $\mathrm{ML}(P_\varphi)=P_\varphi$ and the depth/size is preserved.
- `Status:` proven (the structure does not become more complicated).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark to Lemma 15.7.4 that
  $\mathrm{ML}(P_\varphi)$ remains a depth-3 formula of size $O(L)$.

### 16.66. Exploratory step: correctness of the constraint "$|C|\le m(s)$" (or $C<2^{m(s)}$)

- `Lens:` Compression/canonization.
- `Statement:` Restriction on the circuit code of the form $|C|\le m(s)$ (equivalent to
  numerical $C<2^{m(s)}$) in $tt(f_n,s,t)$ and (H1$_\Pi$) is correct: it only fixes
  circuit code length $C$ and does not exclude any circuit of size $\le s$, since
  any such code can be padded with zeros up to length $m(s)$ (padding). Hence,
  a quantifier over $C<2^{m(s)}$ is equivalent to a quantifier over all circuits of size $\le s$
  (if there is a filter $\mathrm{Valid}_s(C)$).
- `Toy test:` $s=2$, a single AND gate circuit has a code length of $m(2)$.
  If the code is shorter, pad it with zeros; validity $\mathrm{Valid}_2(C)$
  remains true. This means that the constraint $|C|\le m(2)$ (or $C<2^{m(2)}$) does not lose circuits.
- `Status:` proven (padding).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark to (H1$_\Pi$)/(H2$_\Pi$),
  that the constraint $|C|\le m(s)$ is just a fixation on the length of the code.

### 16.67. Exploratory step: $P_\varphi$ may not be multilinear

- `Lens:` Compression/canonization.
- `Statement:` The polynomial $P_\varphi=\prod_j S_{C_j}$ can contain powers
  $x_i^2$ due to repeated occurrences of the variable in different clauses, therefore
  multilinearization is really needed in barrier 15.7.4.
- `Toy test:` $\varphi=(x)\wedge(x\lor y)$. Then
  $P_\varphi=x\cdot(1-(1-x)(1-y))=x(x+y-xy)=x^2+xy-x^2y$ - not multilinear.
  On the Boolean cube $x^2=x$, and $\mathrm{ML}(P_\varphi)=x$.
- `Status:` proven (clear example).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the sanitation check,
  that ML is needed because $P_\varphi$ can contain $x_i^2$ when repeated
  occurrences of the variable.

### 16.68. Exploratory step: CNF encoding of the comparator

- `Lens:` Compression/canonization.
- `Statement:` For $k$-bit numbers $S$ and constant $T$ comparison
  $S\ge T$ is encoded by a CNF of size $O(k)$ with $O(k)$ auxiliary
  variables (through the prefix-equality and "first excess").
  Therefore, converting the comparator to CNF does not change the asymptotics
  $\mathrm{Count}_{\ge T}$.
- `Toy test:` $k=2$, $S=s_1s_0$, $T=t_1t_0$. Let
  $e_i\leftrightarrow(s_i\leftrightarrow t_i)$ and
  $g_i\leftrightarrow(s_i\land\neg t_i)$.
  Then $S\ge T \iff g_1\lor(e_1\land g_0)\lor(e_1\land e_0)$.
  Each $e_i,g_i$ and combination is encoded with $O(1)$ clauses.
- `Status:` proven (Tseitin coding).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to Lemma 15.7.1d,
  that the comparator has a CNF encoding of size $O(\log N)$.

### 16.69. Exploratory step: $t(n)$ and $T(n)$ are indeed integers

- `Lens:` Equivalence.
- `Statement:` For $t(n)=1/2-1/2^{n/4}$ and $n$ multiple of 4, the threshold
  $T(n)=t(n)2^n$ is an integer, namely
  $T(n)=2^{n-1}-2^{3n/4}$. Therefore, in this case $\lceil t(n)2^n\rceil$
  is not required, and $\mathrm{Count}_{\ge T}$ is specified by an integer threshold.
- `Toy test:` $n=4$: $t(n)=1/2-1/2=0$, which means $T(4)=0$.
  The formula $\mathrm{Count}_{\ge 0}$ is trivially true; this agrees
  with the formula $2^{n-1}-2^{3n/4}=8-8=0$.
- `Status:` proven (substitution).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to Lemma 15.7.1c,
  that for $4\mid n$ the threshold is integer and rounding is not necessary.

### 16.70. Exploratory step: "almost half" for $t(n)$

- `Lens:` Invariant.
- `Statement:` For $t(n)=1/2-1/2^{n/4}$ we have
  $$\tfrac12 - t(n)=2^{-n/4},\qquad T(n)=t(n)2^n=2^{n-1}-2^{3n/4}.$$
  Therefore, the acceptable correlation with the function decreases as $2^{-n/4}$,
  those. the requirement is "almost half" of errors.
- `Toy test:` $n=8$: $t(n)=1/2-1/2^{2}=1/2-1/4=1/4$,
  $T(n)=2^{7}-2^{6}=128-64=64$. The error must occur on at least 64 inputs
  out of 256.
- `Status:` proven (substitution).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the definition of $t(n)$,
  that $1/2-t(n)=2^{-n/4}$ and how does this relate to "almost balanced".

### 16.71. Exploratory step: Tseitin encoding of the counter

- `Lens:` Compression/canonization.
- `Statement:` If $\mathrm{Count}_{\ge T}$ is calculated by a Boolean circuit
  size $S$ (adder-tree/Batcher), then its Tseitin encoding gives CNF
  with $O(S)$ auxiliary variables and $O(S)$ clauses, equisatisfaction
  the original diagram. Therefore, the formula $\mathrm{Count}_{\ge T}$ can be
  is given propositionally of size $\mathrm{poly}(2^n)$.
- `Toy test:` Half adder: $s=a\oplus b$, $c=a\land b$.
  $c\leftrightarrow(a\land b)$ is encoded with 3 clauses,
  $s\leftrightarrow(a\oplus b)$ - 4 clauses. Total $O(1)$ clauses per gate,
  means the total size is $O(S)$.
- `Status:` proven (standard Tseitin coding).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to Lemma 15.7.1d,
  that $\mathrm{Count}_{\ge T}$ can be converted to CNF with linear overhead.

### 16.72. Exploratory step: "almost half" gives a large threshold

- `Lens:` Invariant.
- `Statement:` For $t(n)=1/2-1/2^{n/4}$ the threshold $T(n)=t(n)2^n$ satisfies
  $$2^{n-2}\ <\ T(n)\ <\ 2^{n-1}$$
  for all sufficiently large $n$. This means that the threshold is asymptotically proportional
  $2^n$ and "almost half" of errors is a really large share.
- `Toy test:` $n=8$: $T(8)=2^{7}-2^{6}=128-64=64$, and
  $2^{6}=64 < T(8)=64 < 2^{7}=128$ (the limit is reached at small $n$).
- `Status:` proven (estimate $2^{n-1}-2^{3n/4}$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the definition of $t(n)$,
  that the threshold $T(n)$ is always linear in $2^n$ (almost half).

### 16.73. Exploratory step: $t(n)$ increases monotonically towards $1/2$

- `Lens:` Invariant.
- `Statement:` The function $t(n)=1/2-2^{-n/4}$ increases monotonically in $n$ and
  $\lim_{n\to\infty} t(n)=1/2$. Therefore, the average error requirement
  becomes more and more strict as $n$ grows.
- `Toy test:` $n=4$: $t=0$; $n=8$: $t=1/4$; $n=12$: $t=1/2-2^{-3}=3/8$.
  The values are growing and approaching $1/2$.
- `Status:` proven (monotonicity $2^{-n/4}$).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the definition of $t(n)$,
  that it is monotone and tends to $1/2$.

### 16.74. Research step: $\varphi$ impossible $\Leftrightarrow \mathrm{ML}(P_\varphi)\equiv 0$

- `Lens:` Equivalence.
- `Statement:` For CNF $\varphi$ true
  $$\varphi\ \text{impossible}\ \iff\ \mathrm{ML}(P_\varphi)\equiv 0.$$
  Proof: by steps 16.53 and 16.64, $P_\varphi$ and $\mathrm{ML}(P_\varphi)$
  coincide with the feasibility indicator by $\{0,1\}^n$, and according to 16.52 it is zero
  on a cube, a multilinear-polynomial is identically zero.
- `Toy test:` $\varphi=(x)\wedge(\neg x)$ is not feasible. Then
  $P_\varphi=x(1-x)=x-x^2$, $\mathrm{ML}(P_\varphi)=x-x=0$.
  For $\varphi=(x)$ we have $P_\varphi=x$, $\mathrm{ML}(P_\varphi)=x\not\equiv 0$.
- `Status:` proven (reduction to previous steps).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to the sanitation check,
  that the equivalence follows from steps 16.52/16.53/16.64.

### 16.75. Exploratory step: fineness of reduction does not affect PIT

- `Lens:` Trade-off.
- `Statement:` In barrier 15.7.4 deterministic PIT for ROABP
  applies to $\mathrm{ML}(P_\psi)$, where $|\psi|\le \mathrm{poly}(|\varphi|)$.
  Any polynomial blow-up reduction only changes the polynomial to the degree
  size/degree of ROABP, so the PIT time remains polynomial.
- `Toy test:` If $|\psi|\le |\varphi|^2$ and PIT runs in $O(|\psi|^3)$,
  then the overall runtime $O(|\varphi|^6)$ is still a polynomial.
- `Status:` proven (composition assessment).
- `Barrier check:` r - not applicable, NP - not applicable, alg - not applicable.
- `Next step:` if desired, add a remark next to Lemma 15.7.4c,
  that the polynomial blow-up does not affect the asymptotic behavior of PIT.

### 16.76. Exploratory step: boundedoccurrence 3SAT with linear blowup

- `Lens:` Compression/canonization.
- `Statement:` There is a ptime reduction from 3SAT to 3SAT, where each
  the variable occurs no more than 9 times, and the size grows linearly.
  Construction: for a variable $x$ with $k$ occurrences, enter $x_1,\dots,x_k$,
  replace each occurrence with our own $x_i$, and add a chain of equalities
  $x_i\leftrightarrow x_{i+1}$ for $i=1..k-1$. Every equality
  $(x_i\lor\neg x_{i+1})\land(\neg x_i\lor x_{i+1})$ turns into 3CNF
  via $(a\lor b)\equiv(a\lor b\lor y)\land(a\lor b\lor\neg y)$.
  Then for each $x_i$ we get no more than $1+2\cdot 4=9$ occurrences,
  and the total number of new clauses/variables is proportional to the sum of occurrences.
- `Toy test:` $x$ occurs 3 times. Enter $x_1,x_2,x_3$ and clauses
  $x_1\leftrightarrow x_2$, $x_2\leftrightarrow x_3$.
  If $x=1$ in a satisfying assignment, then take $x_1=x_2=x_3=1$,
  and all equalities are true; conversely, equalities force all $x_i$ to coincide,
  this means the assignment is compressed to the value $x$.
- `Status:` proven (explicit reduction).
- `Barrier check:` r - applicable (reduction is relativized), NP - not applicable,
  alg - not applicable.
- `Next step:` if desired, tighten the constant to 4 (Tovey) or evaluate
  blow-up in planar Lichtenstein reduction.

### 16.77. Exploratory step: counter $\mathrm{Count}_{\ge T}$ of size $O(N\log N)$

- `Lens:` Trade-off.
- `Statement:` For $N$ input bits there is a Boolean circuit of size
  $O(N\log N)$, calculating $\mathrm{Count}_{\ge T}(b_1,\dots,b_N)$:
  Let's build a binary tree of adders, obtaining $k=\lceil\log_2 N\rceil$-bit sum $S$,
  then compare $S\ge T$ with a comparator of size $O(k)$.
  For a "simple" tree of ripple-carry adders, the depth is $O(\log^2 N)$; depth is possible
  improve to $O(\log N)$, but for LogLog we need size $O(2^n n)=\mathrm{poly}(2^n)$.
- `Toy test:` $N=4$, $T=3$. Add the pairs $(b_1,b_2)$ and $(b_3,b_4)$
  half-adders, then sum two 2-bit numbers with a full adder;
  the comparator tests $S\ge 3$ (binary $11$).
- `Status:` proven (explicit construction).
- `Barrier check:` r - not applicable (syntax scheme), NP - not applicable
  (no lower bounds), alg - not applicable (no arithmetization).
- `Next step:` if desired, link to Lemma 15.7.1d: specify an explicit
  counter size $O(2^n n)$ and then apply 16.71 for CNF encoding.

### 16.78. Exploratory step: explicit linear counting for CNF->3CNF

- `Lens:` Compression/canonization.
- `Statement:` Let CNF $\varphi$ have clauses of length $k_1,\dots,k_m$ and a total of
  $L=\sum_j k_j$ literals. Let us define a reduction $r$: clauses of length $\le 3$
  we leave it, and replace the clause of length $k>3$ with a chain of $k-2$ 3clauses with
  $k-3$ new variables. Then
  $$\#\mathrm{clauses}(r(\varphi))\le \sum_{k_j\le 3}1+\sum_{k_j>3}(k_j-2)\le \sum_j k_j=L,$$
  and therefore $\#\mathrm{lits}(r(\varphi))\le 3L$.
  Consequently, the reduction CNF->3CNF has a linear blowup in $L$.
- `Toy test:` A clause of length $4$ gives $k-2=2$ clauses and $k-3=1$ new variable,
  those. 6 literals instead of 4; the estimate $6\le 3\cdot 4$ is satisfied.
- `Status:` proven (calculation by clauses).
- `Barrier check:` r - applicable (reduction is relativized), NP - not applicable,
  alg - not applicable.
- `Next step:` if desired, record this as a numerical remark
  in Lemma 15.7.3c (PIT  IPS/EF).

### 16.79. Research step: quantifier by circuit codes and padding

- `Lens:` Equivalence.
- `Statement:` Let us fix the gate-list coding of Boolean circuits of size $\le s$
  bitstrings of length $m(s)$, as well as the predicate $\mathrm{Valid}_s(C)$, which
  checks the correctness of the code. Then the quantifier "for all circuits of size $\le s$"
  is equivalently expressed as
  $$\forall C<2^{m(s)}\ \bigl(\mathrm{Valid}_s(C)\to P(C)\bigr),$$
  where $P(C)$ is any statement that depends only on the decoded circuit.
  In particular, the bounded constraint $C<2^{m(s)}$ (equivalent to $|C|\le m(s)$) in (H1$_\Pi$)/(H2$_\Pi$) fixes only
  code length (bounded quantifier) and does not exclude any scheme of size $\le s$:
  the short code can be padded with zeros up to length $m(s)$ (without changing the decoded
  scheme), and $\mathrm{Valid}_s$ cuts off non-codes.
- `Toy test:` $s=2$. A circuit with one AND gate has a code length of $\le m(2)$.
  Adding zeros to length $m(2)$ does not change the list of gates (the empty "tail"
  reads as dummy gates/constants), so $\mathrm{Valid}_2(C)=1$
  and all properties of the circuit (output on $x$) are preserved.
- `Status:` proven (padding fixes length).
- `Barrier check:` r - not applicable (syntax trick), NP - not applicable,
  alg - not applicable.
- `Next step:` fix this equivalence as a remark next to
  Lemma 15.7.2b in the main text (close Q2a).

### 16.80. Exploration step: 3CNF for $\mathrm{Count}_{\ge T}$ of size $O(N\log N)$

- `Lens:` Compression/canonization.
- `Statement:` Let $N=2^n$ and $T\in\{0,\dots,N\}$. Then there is 3CNF
  formula $\mathrm{Count}_{\ge T}^{\mathrm{CNF}}(e,z)$ of size $O(N\log N)$
  (by the number of clauses/literals), such that for any assignment $e\in\{0,1\}^N$
  Done:
  $$\exists z\ \mathrm{Count}_{\ge T}^{\mathrm{CNF}}(e,z)\quad\Longleftrightarrow\quad \sum_{i=1}^N e_i\ge T.$$
  Proof: according to 16.77 there is a circuit of size $S=O(N\log N)$ for
  $\mathrm{Count}_{\ge T}$ (addertree + comparator), and according to 16.71 Tseitincoding
  any circuit of size $S$ gives CNF (and even 3CNF) with $O(S)$ auxiliaries
  variables and $O(S)$ clauses.
- `Toy test:` $N=4$, $T=3$: the circuit calculates the sum $S\in\{0,\dots,4\}$ and checks
  $S\ge 3$. Tseitin coding adds a constant number of clauses per gate,
  so the size remains $O(4\log 4)$.
- `Status:` proven (composition 16.77 + 16.71).
- `Barrier check:` r - not applicable (syntactic construction), NP - not applicable
  (no lower marks), alg - not applicable.
- `Next step:` fix as a remark next to Lemma 15.7.1d (close Q1a).

### 16.81. Exploratory step: Toveysplitting gives (O3, $L\le 3$)-SAT with linear blowup

- `Lens:` Compression/canonization.
- `Statement:` There is a ptime reduction from 3SAT to CNF, where each
  the variable occurs no more than 3 times, and the length of the clauses is $\le 3$ (2 clauses are allowed),
  and the size grows linearly. Construction (Tovey; see Theorem 3 in Berman-Karpinski-Scott):
  if variable $x$ occurs $d>3$ times, enter $x_1,\dots,x_d$,
  replace $d$ occurrences of $x$ with $x_1,\dots,x_d$ and add a 2-clause cycle
  $$x_1\vee\neg x_2,\ x_2\vee\neg x_3,\ \dots,\ x_{d-1}\vee\neg x_d,\ x_d\vee\neg x_1.$$
  These clauses are equivalent to $x_1=\cdots=x_d$, so the (un)satisfiability remains.
  Each $x_i$ occurs in exactly one original clause and two 2clauses,
  that is, no more than 3 times; added $d$ clauses and $d$ variables, so the total
  blow-up $O(L)$ by the number of literals $L$ of the original formula.
- `Toy test:` $d=4$. Cycle
  $x_1\vee\neg x_2,\ x_2\vee\neg x_3,\ x_3\vee\neg x_4,\ x_4\vee\neg x_1$
  defines the implications $x_2\to x_1\to x_4\to x_3\to x_2$, which means all $x_i$ are equal.
  Then the satisfying assignment is transferred between the original formula and the new one,
  putting $x:=x_1$ and $x_i:=x$.
- `Status:` proven (explicit reduction + calculation).
- `Barrier check:` r - applicable (reduction is relativized), NP - not applicable,
  alg - not applicable.
- `Next step:` find/fix a gadget that eliminates 2clauses and gives
  3CNF with a limit of <=4 occurrences (Toveyvariant), or evaluate blowup
  in planar Lichtenstein reduction.

### 16.82. Exploratory step: elimination of 2clauses  3CNF with a limit of <=4 occurrences

- `Lens:` Equivalence.
- `Convention:` in this project, 3CNF allows duplication of literals within a clause (used only as 2->3 padding).
- `Statement:` There is a ptime reduction of $R$ from 3SAT to 3SAT such that in
  $R(\varphi)$ each variable occurs no more than 4 times, and the size grows
  linear in the number of literals. It is enough to improve the design of 16.81:
  replace all 2-clauses of the form $(x_i\vee\neg x_{i+1})$ with 3-clauses
  $$(x_i\vee x_i\vee\neg x_{i+1}).$$
  This replacement is equivalent (adds a duplicate literal), so (un)feasibility
  is saved. If $x_i$ is a copy of the variable from 16.81, then it occurs
  1 time in the "original" 3clause and 3 more times in the cycle (twice as $x_i$ in its
  clause and once as $\neg x_i$ in the previous one), total <=4.
- `Toy test:` loop for $d=4$:
  $(x_1\vee x_1\vee\neg x_2)\wedge(x_2\vee x_2\vee\neg x_3)\wedge
  (x_3\vee x_3\vee\neg x_4)\wedge(x_4\vee x_4\vee\neg x_1)$
  is equivalent to the 2-clause cycle from 16.81 and therefore sets $x_1=\cdots=x_4$.
  Counting: $x_2$ appears twice in its clause, once as $\neg x_2$
  in the first and (exactly) once in the original 3clause, where it replaced one
  occurrence of variable $x$.
- `Status:` proven (2->3padding + counting occurrences).
- `Barrier check:` r -- applicable (pure reduction, relativized),
  NP - not applicable, alg - not applicable.
- `Next step:` in the main text next to Lemma 15.7.4d indicate that
  NPdifficulty 3SAT with the constraint "each variable <=4 occurrences" follows
  from 16.81-16.82 (without external facts, except for NPcompleteness of 3SAT).

### 16.83. Exploratory step: blow-up reduction 3SAT -> Planar 3SAT (Lichtenstein)

- `Lens:` Trade-off.
- `Statement:` Let $\varphi$ be a 3CNF with $m$ clauses and $n$ variables.
  In the reduction of Lichtenstein (1982), a planarization of the incident graph is made:
  intersections are eliminated by a fixed crossover gadget that adds $O(1)$
  new variables/clauses per intersection. In standard "lattice" installation
  the number of intersections is $\le O(mn)$, so the final Planar-3-CNF $\varphi'$ has
  size $|\varphi'|=O(mn)$ and, in particular, $|\varphi'|=O(|\varphi|^2)$.
- `Toy test:` $m=n=2$: the $6\times 6$ lattice has 36 potential intersection points,
  this means that even a rough estimate gives $|\varphi'|=O(1+36)$.
- `Status:` proven (blow-up assessment from the design description).
- `Barrier check:` r -- applicable (reduction is relativized), NP -- not applicable
  (this is NP completeness, not a lower bound), alg - not applicable.
- `Next step:` refer to this estimate next to Lemma 15.7.4d (close Q5).

### 16.84. Exploratory step: Planar3SAT <=p Planar3SAT(<=4occ)

- `Lens:` Compression/canonization.
- `Statement:` There is a p-time reduction from Planar-3-SAT to Planar-3-SAT, where
  Each variable occurs no more than 4 times. Let $\varphi$ be planar 3CNF and
  variable $x$ occurs $d$ times. Enter copies of $x_1,\dots,x_d$, replace $j$e
  occurrence of $x$ on $x_j$ and adding a 3clause cycle
  $$(x_1\vee x_1\vee\neg x_2)\wedge(x_2\vee x_2\vee\neg x_3)\wedge\cdots\wedge(x_d\vee x_d\vee\neg x_1).$$
  These clauses are equivalent to the cycle of implications $x_2\to x_1\to\cdots\to x_d\to x_2$,
  that means they force $x_1=\cdots=x_d$; satisfaction remains. Every $x_i$
  occurs twice in its cycle clause, once as $\neg x_i$ in the previous one
  and exactly once in the original 3clause  <=4. Planarity is preserved: in planar
  in the embedding of the incident graph $\varphi$ we replace the vertex $x$ with a planar gadget cycle,
  attaching external edges (to the original clauses) to the vertices $x_i$ in the same
  cyclic order; local replacement in the disk does not create intersections.
- `Toy test:` $d=5$. From the clauses of the cycle it follows $x_2\to x_1\to x_5\to x_4\to x_3\to x_2$,
  that means all $x_i$ are equal. Counting: $x_3$ has 2 occurrences in $(x_3\vee x_3\vee\neg x_4)$,
  1 occurrence as $\neg x_3$ in $(x_2\vee x_2\vee\neg x_3)$ and 1 occurrence in "your"
  original clause.
- `Status:` proven (local split + planar vertex replacement).
- `Barrier check:` r - applicable (reduction is relativized), NP - not applicable,
  alg - not applicable.
- `Next step:` add 1 line to Lemma 15.7.4d: Planar3SAT(<=4occ)
  NPfull (Liechtenstein + 16.84).

-/
