import Paperproof

/-!

# P vs NP - research steps 16.3-16.36

Main index: `P_vs_NP.md`.

### 16.3. Research step: decision vs search for SAT

**Question ("What if...?").** Can SAT be solved in polynomial time,
and the task of finding a satisfying assignment remains significantly more difficult?

**Definition (SATSEARCH).** Given the input of the CNF formula $\varphi$: if $\varphi$ is satisfiable,
issue a satisfying assignment; otherwise print $\bot$.

**Lemma 16.3.** There is a polynomial algorithm that solves SATSEARCH,
using $O(n)$ calls to solve the SAT (where $n$ is the number of variables).
In particular, if $\mathrm{SAT}\in\mathrm{P}$, then SATSEARCH $\in\mathrm{FP}$.

*Proof.* First, we check with one call whether $\varphi$ is executable.
If not, return $\bot$.
Otherwise, we fix the variables sequentially: for $i=1..n$ we check the satisfiability
$\varphi\upharpoonright (x_i=0)$. If feasible, set $x_i:=0$,
otherwise $x_i:=1$ (in this case $\varphi\upharpoonright (x_i=1)$ must be satisfiable,
otherwise the original $\varphi$ is unsatisfiable). By induction on $i$ satisfiability is preserved,
and after $n$ steps we obtain a satisfying assignment.
Time - $O(n)$ of SAT calls and polynomial substitutions. $\square$

**Conclusion.** An attempt to separate P and NP through "decision is simpler than search"
does not work for SAT: SAT is self-reducing.

**Barrier check.**
- *Relativization:* yes, the algorithm is oracle (same argument for $\mathrm{SAT}^A$).
- *Natural proofs:* not applicable (no schematic lower estimates).
- *Algebrization:* not applicable (no algebraization/polynomials; purely combinatorics).

### 16.4. Research step: sparse NPcomplete  P=NP

**Question ("What if...?").** What if NP has a sparse NP-complete language?

**Definition (sparse).** A language $S$ is sparse if there exists a polynomial $p$ such that
$|S\cap \Sigma^{\le m}|\le p(m)$ for all $m$.

**Lemma 16.4 (Mahany).** If there is a sparse NP-complete language
relative to $\le_m^p$, then $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $S$ sparse and $\mathrm{SAT}\le_m^p S$ through $f$.
Let us fix a polynomial $p$ for sparsity and a polynomial $q$ limiting the length $f(\psi)$
on formulas $\psi$ of size $\mathrm{poly}(|\varphi|)$.
Let $K:=p(q(|\varphi|))$. Let's build the SAT algorithm.

We support a list of $L$ formulas with an invariant:
(i) $|L|\le K$, (ii) if $\varphi$ is satisfiable, then at least one formula from $L$ is satisfiable.
Start: $L=\{\varphi\}$. For the variable $x_i$ we replace each $\psi\in L$
on $\psi\upharpoonright(x_i=0)$ and $\psi\upharpoonright(x_i=1)$,
getting $L'$, then we apply "pruning".
(If we need to stay in CNF, we use standard Tseitin polynomial encoding of disjunctions.)

**Pruning lemma.** For the list $\varphi_1,\dots,\varphi_k$ (where $k> K$) we can use the polynomial
time to remove at least one formula, keeping (ii).

Proof pruning: put $\psi_i:=\varphi_1\lor\cdots\lor\varphi_i$ and $y_i:=f(\psi_i)$.
- If $i<j$ with $y_i=y_j$ are found, then $\psi_i$ and $\psi_j$ have the same satisfiability,
  so removing $\varphi_{i+1},\dots,\varphi_j$ preserves (ii).
- Otherwise, all $y_i$ are different. Then among $\psi_i$ satisfiable $\le K$ (otherwise in $S$ there would be
  $>K$ different lines). Satisfiable $\psi_i$ form a suffix, which means that if there is
  of a satisfiable formula it is among the last $K$; remove the first $k-K$.

Repeating pruning, hold $|L|\le K$. After processing all variables, all formulas in $L$
constant; we check whether it is true. This is polynomial, which means $\mathrm{SAT}\in\mathrm{P}$,
hence $\mathrm{P}=\mathrm{NP}$. $\square$

**Barrier check.**
- *Relativization:* yes (the argument remains true with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

### 16.5. Research step: pbounded resolution?

**Question ("What if...?").** Can a resolution be p-bounded for everyone
unsatisfiable CNF formulas?

**Lemma 16.5.** If the resolution is p-bounded, then $\mathrm{NP}=\mathrm{coNP}$.

*Proof.* With a pbounded resolution, every unsatisfiable CNF
has a polynomial refutation. Checking the correctness of the resolution conclusion
is polynomial, which means $\mathrm{UNSAT}\in\mathrm{NP}$.
Since $\mathrm{UNSAT}$ is coNP-complete, we obtain $\mathrm{coNP}\subseteq\mathrm{NP}$,
which means $\mathrm{NP}=\mathrm{coNP}$. $\square$

**Counterexample to the premise.** Formulas $\mathrm{PHP}^{n}_{n+1}$ require
exponential resolution refutations (Theorem 15.2),
so the resolution is not p-bounded in general.

**Barrier check.**
- *Relativization:* not applicable (statement about a fixed proofsystem).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.6. Exploratory step: resolution vs CP (psimulation)

**Question ("What if...?").** Can resolution psimulate a Cutting Planes (CP) system?

**Lemma 16.6.** Resolution does not p-simulate CP.

*Proof (counterexample).* Suppose that resolution psimulates CP.
Then any CP refutation of size $\mathrm{poly}(n)$ can be transformed
into a resolution refutation of size $\mathrm{poly}(n)$.
By Theorem 15.8, the formulas $\mathrm{PHP}^{n}_{n+1}$ have polynomial CP refutations,
and by Theorem 15.2 any resolution refutation $\mathrm{PHP}^{n}_{n+1}$
has exponential size. Contradiction. $\square$

**Barrier check.**
- *Relativization:* not applicable (statement about a specific proofsystem).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.7. Exploratory Step: Approaching MAX3SAT

**Question ("What if...?").** What if there is a polynomial algorithm,
which distinguishes satisfiable 3CNFs from formulas where it cannot be satisfied
more than $(1-\varepsilon)$ fraction of clauses (for some constant $\varepsilon>0$)?

**Definition (GAP3SAT$_\varepsilon$).** Input - 3CNF $\varphi$.
YES: $\varphi$ is feasible. NO: any substitution satisfies
no more than $(1-\varepsilon)$ fraction of clauses.

**Lemma 16.7.** If for some $\varepsilon>0$ the problem GAP-3SAT$_\varepsilon$
is solved in polynomial time, then $\mathrm{P}=\mathrm{NP}$.

*Proof.* By the PCP theorem (Section 16.2), there is a constant
$\varepsilon>0$, for which GAP-3SAT$_\varepsilon$ is NP-hard.
If it were solved in polynomial time, then SAT would be solved,
hence $\mathrm{P}=\mathrm{NP}$. $\square$

**Barrier check.**
- *Relativization:* does not have to relativize (PCP uses arrhythmeticization).
- *Natural proofs:* not applicable (these are not schematic lower bounds).
- *Algebrization:* not clear; the proof of PCP does not reduce to pure algebrization.

### 16.8. Research step: NP and coNPcompleteness of one language

**Question ("What if...?").** Could there be a language $L$ that
Is NPcomplete and coNPcomplete (by $\le_m^p$)?

**Lemma 16.8.** If there is a language that is both NP-complete and coNP-complete
(by $\le_m^p$), then $\mathrm{NP}=\mathrm{coNP}$.

*Proof.* Let $L$ be such a language. Then $L\in\mathrm{NP}\cap\mathrm{coNP}$.
For any $A\in\mathrm{NP}$ there is a polynomial reduction of $f$ such that
$x\in A \iff f(x)\in L$. Then
$$x\in A^c \iff f(x)\in L^c.$$
Since $L\in\mathrm{coNP}$, we have $L^c\in\mathrm{NP}$, therefore $A^c\in\mathrm{NP}$,
that is, $A\in\mathrm{coNP}$. Therefore, $\mathrm{NP}\subseteq\mathrm{coNP}$.
Symmetrically, from the coNP-completeness of $L$ and the fact that $L\in\mathrm{NP}$, we obtain
$\mathrm{coNP}\subseteq\mathrm{NP}$. So $\mathrm{NP}=\mathrm{coNP}$. $\square$

**Barrier check.**
- *Relativization:* yes (the argument is preserved for oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.9. Research step: SAT <= UNSAT?

**Question ("What if...?").** Can SAT be polynomially reduced to UNSAT?

**Lemma 16.9.** If $\mathrm{SAT}\le_m^p\mathrm{UNSAT}$, then $\mathrm{NP}=\mathrm{coNP}$.

*Proof.* Let $f$ be the reduction of SAT to UNSAT.
Then SAT belongs to coNP (coNP is closed under $\le_m^p$-reductions).
Since SAT is NP-complete, we obtain $\mathrm{NP}\subseteq\mathrm{coNP}$.
We take the additions: $\mathrm{coNP}\subseteq\mathrm{NP}$. Therefore, $\mathrm{NP}=\mathrm{coNP}$. $\square$

**Barrier check.**
- *Relativization:* yes (the argument is preserved for oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.10. Exploratory Step: Unique-SAT and Randomization

**Question ("What if...?").** What if Unique-SAT is solved in polynomial time - should $\mathrm{P}=\mathrm{NP}$?

**Definition (Unique-SAT, promise).** Input: CNF formula $\varphi$ over $n$ variables.
YES: $\varphi$ has exactly one satisfying assignment.
NO: $\varphi$ has no satisfying assignments.
(Other cases do not need to be handled correctly.)

**Lemma 16.10 (Valiant-Vazirani).** There is a probabilistic polynomial reduction,
which, using the formula $\varphi$, constructs a CNF formula $\varphi'$ such that:
- if $\varphi$ is unsatisfiable, then $\varphi'$ is always unsatisfiable;
- if $\varphi$ is satisfiable, then with probability $\ge 3/(16(n{+}1))=\Omega(1/n)$ $\varphi'$ has exactly one solution.

In particular, if Unique-SAT $\in\mathrm{P}$ then $\mathrm{SAT}\in\mathrm{RP}$.

*Proof.* Let $S\subseteq\{0,1\}^n$ be the set of solutions to $\varphi$, $s=|S|$.
We choose $m\in\{1,\dots,n{+}1\}$, a random pairwise independent hash function
$h:\{0,1\}^n\to\{0,1\}^m$ (for example, $h(x)=Ax\oplus b$ over $\mathbb{F}_2$)
and random $t\in\{0,1\}^m$. We are building
$$\varphi' := \varphi\land (h(x)=t),$$
encoding $m$ linear equations in CNF with polynomial growth (Tseitin encoding).
If $\varphi$ is unsatisfiable, then so is $\varphi'$.

Let $s\ge 1$. There is $m$ such that $2^{m-2}< s\le 2^{m-1}$.
Let $Z=|S\cap h^{-1}(t)|=\sum_{x\in S} I_x$, where $I_x=[h(x)=t]$.
Then $\mu=\mathbb{E}[Z]=s/2^m\in(1/4,1/2]$ and by pairwise independence
$$\mathbb{E}[Z(Z-1)]=\sum_{x\ne y}\Pr[I_x=I_y=1]=\frac{s(s-1)}{2^{2m}}\le \mu^2.$$
Since for $Z\ge 2$ $Z(Z-1)\ge Z$ holds, we obtain
$$\Pr[Z=1]\ge \mu-\mathbb{E}[Z(Z-1)]\ge \mu-\mu^2\ge 3/16.$$
Therefore, for the "correct" $m$ the probability of uniqueness is $\ge 3/16$.
With a uniform choice of $m\in\{1,\dots,n{+}1\}$ we obtain success
$$\Pr[\text{unique}]\ \ge\ \frac{3}{16(n+1)}=\Omega(1/n).$$
By repetition (strengthening) we obtain the RP algorithm in the presence of the Unique-SAT solver. $\square$

**Output/failure.** Unique-SAT $\in\mathrm{P}$ gives only $\mathrm{SAT}\in\mathrm{RP}$.
To get $\mathrm{P}=\mathrm{NP}$, we need derandomization (for example, $\mathrm{RP}=\mathrm{P}$)
or deterministic "isolation" of decisions.

**Barrier check.**
- *Relativization:* yes (the reduction is combinatorial and transfers to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable/not obvious.

### 16.11. Exploratory step: NP  BPP  PH collapse

**Question ("What if...?").** What if SAT (or the entire NP) is solved in BPP - does polynomial hierarchy collapse follow?

**Definition (BPP).** Language $L\in\mathrm{BPP}$ if there is a probabilistic
polynomial machine $A$, which for all $x$:
$$x\in L\Rightarrow \Pr[A(x)=1]\ge 2/3,\quad x\notin L\Rightarrow \Pr[A(x)=0]\ge 2/3.$$

**Lemma 16.11.** If $\mathrm{NP}\subseteq\mathrm{BPP}$, then $\mathrm{PH}\subseteq\mathrm{BPP}$.
(In particular, if $\mathrm{SAT}\in\mathrm{BPP}$, then $\mathrm{PH}$ collapses into BPP.)

*Proof.* First we show $\mathrm{BPP}^{\mathrm{BPP}}=\mathrm{BPP}$.
Let $M^{O}$ be a BPP machine making at most $q(n)$ requests to the oracle $O\in\mathrm{BPP}$.
Without loss of generality, let us strengthen $M$ (by standard repetition and majority) so that with an ideal oracle
the error $M$ becomes $\le 1/10$; the number of requests in this case increases only by $O(1)$ times and is absorbed by $q(n)$.
Each request $y$ is simulated by the algorithm $A_O(y)$, strengthening it to the point of error
$\delta:=1/(10q(n))$ by repeating $O(\log q(n))$ times and majority voting.
By union bound, the chance that at least one of the oracle's answers
is erroneous and does not exceed $q(n)\cdot\delta\le 1/10$.
Conventionally, given the correct answers of the oracle, $M$ is wrong with probability $\le 1/10$.
In total, the total error is $\le 1/5<1/3$, and the time remains polynomial.
Therefore, $\mathrm{BPP}^{\mathrm{BPP}}\subseteq\mathrm{BPP}$;
the reverse inclusion is trivial.

Now induction on $k$ for $\Sigma_k^p$.
Base: $\Sigma_1^p=\mathrm{NP}\subseteq\mathrm{BPP}$ by assumption.
Transition: if $\Sigma_k^p\subseteq\mathrm{BPP}$, then
$$\Sigma_{k+1}^p=\mathrm{NP}^{\Sigma_k^p}\subseteq\mathrm{BPP}^{\mathrm{BPP}}=\mathrm{BPP}.$$
This means that all PH levels lie in BPP, i.e. $\mathrm{PH}\subseteq\mathrm{BPP}$. $\square$

**Conclusion/failure.** Assumption $\mathrm{SAT}\in\mathrm{BPP}$ does not give $\mathrm{P}=\mathrm{NP}$,
but only the collapse of PH in BPP. For $\mathrm{P}=\mathrm{NP}$ derandomization is needed
(for example, $\mathrm{BPP}=\mathrm{P}$).

**Barrier check.**
- *Relativization:* yes (argument persists with oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.12. Research step: BPP in Sigma2 cap Pi2 (Sipser-Gacs-Lautemann)

**Question ("What if...?").** Is it possible to place BPP on the second PH level?

**Lemma 16.12 (Sipser-Gacs-Lautemann).** $\mathrm{BPP}\subseteq\Sigma_2^p\cap\Pi_2^p$.

*Proof.* Let $L\in\mathrm{BPP}$. There is a probabilistic machine $R(x,r)$,
running for $\mathrm{poly}(|x|)$ and using $m$ random bits, such that
error $\le 1/3$. Strengthen (repetition and majority) to the point of error
$\varepsilon:=2^{-2n}$, where $n=|x|$; this gives the new $m=\mathrm{poly}(n)$.
Let us set $G_x:=\{r\in\{0,1\}^m:\ R(x,r)=1\}$.
Then
$$x\in L\Rightarrow |G_x|\ge (1-\varepsilon)2^m,\quad x\notin L\Rightarrow |G_x|\le \varepsilon 2^m.$$

Let us fix $k:=m+1$. For $r_1,\dots,r_k\in\{0,1\}^m$, consider
$$U:=\bigcup_{i=1}^k (G_x\oplus r_i),$$
where $\oplus$ is a bitwise XOR.

(1) Let $x\in L$. Let us choose $r_i$ uniformly and independently. For fixed $z$
$$\Pr[z\notin U]=(1-|G_x|/2^m)^k\le \varepsilon^k.$$
By joint probability
$$\Pr[U\ne\{0,1\}^m]\le 2^m\varepsilon^k\le 2^m\cdot 2^{-2n(m+1)}<1.$$
Therefore, there is a set $r_1,\dots,r_k$ with $U=\{0,1\}^m$.

(2) Let $x\notin L$. Then for any $r_1,\dots,r_k$ we have
$|U|\le k|G_x|\le k\varepsilon 2^m<2^m$ (since $k=\mathrm{poly}(n)$ and $\varepsilon=2^{-2n}$; small $n$ can be hardcoded),
then there is $z$ with $z\notin U$.

So,
$$x\in L\iff \exists r_1,\dots,r_k\ \forall z\ \bigvee_{i=1}^k R(x,z\oplus r_i)=1,$$
that there is a $\Sigma_2^p$-formula (since $k,m=\mathrm{poly}(n)$).
Since $\mathrm{BPP}$ is closed by complement, we also obtain
$L\in\Pi_2^p$. So $\mathrm{BPP}\subseteq\Sigma_2^p\cap\Pi_2^p$. $\square$

**Conclusion/failure.** The lemma only places $\mathrm{BPP}$ in the second level of PH;
by itself it does not give $\mathrm{P}=\mathrm{NP}$.

**Barrier check.**
- *Relativization:* yes (the argument is combinatorial, transferable to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.13. Exploratory step: NP in BPP => PH = Sigma2^p

**Question ("What if...?").** If $\mathrm{NP}\subseteq\mathrm{BPP}$, does PH collapse at the second level?

**Lemma 16.13.** If $\mathrm{NP}\subseteq\mathrm{BPP}$, then
$$\mathrm{PH}=\Sigma_2^p=\Pi_2^p.$$

*Proof.* By Lemma 16.11 we obtain $\mathrm{PH}\subseteq\mathrm{BPP}$.
By Lemma 16.12 we have $\mathrm{BPP}\subseteq\Sigma_2^p\cap\Pi_2^p$.
Hence,
$$\mathrm{PH}\subseteq\Sigma_2^p\cap\Pi_2^p\subseteq\Sigma_2^p.$$
But $\Sigma_2^p\subseteq\mathrm{PH}$ by definition, means
$\mathrm{PH}=\Sigma_2^p$. Similar to $\mathrm{PH}=\Pi_2^p$.
Therefore, $\Sigma_2^p=\Pi_2^p$. $\square$

**Conclusion/failure.** Even with $\mathrm{NP}\subseteq\mathrm{BPP}$ we only get PH collapse
at level 2; this does not lead to $\mathrm{P}=\mathrm{NP}$ without derandomization
(for example, $\mathrm{BPP}=\mathrm{P}$).

**Barrier check.**
- *Relativization:* yes (relativizing steps 16.11 and 16.12 are used).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.14. Research Step: SAT to RP => NP = RP

**Question ("What if...?").** What if SAT is solved in RP - does $\mathrm{NP}=\mathrm{RP}$ follow?

**Definition (RP).** Language $L\in\mathrm{RP}$, if there is a probabilistic
polynomial machine $A$, which for all $x$:
$$x\in L\Rightarrow \Pr[A(x)=1]\ge 1/2,\quad x\notin L\Rightarrow \Pr[A(x)=1]=0.$$

**Lemma 16.14.** If $\mathrm{SAT}\in\mathrm{RP}$, then $\mathrm{NP}=\mathrm{RP}$.

*Proof.* (1) $\mathrm{RP}\subseteq\mathrm{NP}$: Let $A$ use $m(n)$ random bits.
NMT guesses the string $r\in\{0,1\}^{m(n)}$ and accepts if and only if
when $A(x,r)=1$. If $x\in L$, there is a receiving $r$;
if $x\notin L$, there are no acceptors of $r$.

(2) $\mathrm{NP}\subseteq\mathrm{RP}$ for $\mathrm{SAT}\in\mathrm{RP}$:
let $L\in\mathrm{NP}$ and $f$ be a polynomial many-one reduction of $L\le_m^p\mathrm{SAT}$.
The algorithm for $L$ computes $y=f(x)$ and runs the RP algorithm for SAT on $y$.
If $x\notin L$, then $y$ is unsatisfiable and the RP algorithm always rejects.
If $x\in L$, then $y$ is feasible and the RP algorithm accepts with probability $\ge 1/2$.
So $L\in\mathrm{RP}$.

So $\mathrm{NP}=\mathrm{RP}$. $\square$

**Conclusion/failure.** Even if SAT is in RP, we only get $\mathrm{NP}=\mathrm{RP}$,
rather than $\mathrm{P}=\mathrm{NP}$ without derandomization (e.g. $\mathrm{RP}=\mathrm{P}$).

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.15. Research Step: P-uniform Schemes for SAT

**Question ("What if...?").** What if SAT has polynomial P-uniform circuits?

**Definition (P-uniform).** A family of circuits $\{C_n\}$ is called P-uniform if
there is a deterministic polynomial machine $U$ whose input is $1^n$
displays a description of the $C_n$ circuit.

**Lemma 16.15.** If SAT has a P-uniform family of circuits of polynomial size,
then $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $U$ construct $C_n$ for $\mathrm{poly}(n)$.
At the input of a formula $\varphi$ of length $n$, we evaluate $C_n$ using $U$ and then
calculate $C_n(\varphi)$ in time $\mathrm{poly}(n)$ (the size of the circuit is polynomial).
Therefore, $\mathrm{SAT}\in\mathrm{P}$, which means $\mathrm{P}=\mathrm{NP}$. $\square$

**Counterexample to the gain.** You cannot replace P-uniform with $\mathrm{P/poly}$.
There is a tally language $L\subseteq\{1\}^*$ that is not in $\mathrm{P}$
(diagonalization as in the time hierarchy theorem, Section 12).
For each $n$, the non-uniform circuit can hardwire the bit $b_n=[1^n\in L]$ and check whether
whether the input is equal to $1^n$ (e.g. AND all $n$ bits), so $L$ is solved by a circuit of size $O(n)$ over length $n$.
Therefore, $L\in\mathrm{P/poly}$, but $L\notin\mathrm{P}$.

**Conclusion/failure.** Polynomial non-uniform schemes do not produce $\mathrm{P}=\mathrm{NP}$;
uniformity of construction is critical.

**Barrier check.**
- *Relativization:* yes (argument - simulation and diagonalization).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.16. Research step: P-immune in NP

**Question ("What if...?").** What if there is a P-immune language in NP?

**Definition (P-immune).** An infinite language $L$ is called a P-immune if it does not have
infinite subset in $\mathrm{P}$.

**Lemma 16.16.** If there is a P-immune language $L\in\mathrm{NP}$, then $\mathrm{P}\ne\mathrm{NP}$.

*Proof.* Assume the opposite: $\mathrm{P}=\mathrm{NP}$. Then $L\in\mathrm{P}$.
But then $L$ is itself an infinite subset of $L$ lying in $\mathrm{P}$,
which contradicts P-immunity. Therefore, $\mathrm{P}\ne\mathrm{NP}$. $\square$

**Counterexample to gain.** NP-completeness does not mean P-immune. For example, the SAT has
infinite subset in $\mathrm{P}$: formulas of the form
$$\bigwedge_{i=1}^m (x_i\lor\neg x_i)$$
are always feasible and can be recognized in polynomial time. Therefore, SAT is not P-immune.

**Barrier check.**
- *Relativization:* yes (argument persists with oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.17. Research step: P-bi-immune in NP

**Question ("What if...?").** What if there is a P-bi-immune language in NP?

**Definition (P-bi-immune).** An infinite language $L$ is called P-bi-immune if
$L$ and $\overline{L}$ are P-immune.

**Lemma 16.17.** If there is a P-bi-immune language $L\in\mathrm{NP}$, then $\mathrm{P}\ne\mathrm{NP}$.

*Proof.* Assume the opposite: $\mathrm{P}=\mathrm{NP}$. Then $L\in\mathrm{P}$.
Since $\mathrm{P}$ is closed by complement, we have $\overline{L}\in\mathrm{P}$.
But then both $L$ and $\overline{L}$ contain infinite subsets in $\mathrm{P}$
(themselves), which contradicts P-immune. Therefore, $\mathrm{P}\ne\mathrm{NP}$. $\square$

**Counterexample to amplification.** NP-completeness does not mean P-bi-immune. For SAT there is
an infinite subset in $\mathrm{P}$, for example formulas
$$\bigwedge_{i=1}^m (x_i\lor\neg x_i),$$
and for $\overline{\mathrm{SAT}}$ there is an infinite subset in $\mathrm{P}$, for example
$$\bigwedge_{i=1}^m (x_i\land\neg x_i).$$
Therefore, SAT is not P-bi-immune.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.18. Exploratory step: NP-hard P-selective

**Question ("What if...?").** What if there is a P-selective language that is NP-hard in $\le_m^p$?

**Definition (P-selective).** A language $S$ is called P-selective if it exists
deterministic polynomial function $s(x,y)$ returning $x$ or $y$ such that
if $x\in S$ or $y\in S$, then $s(x,y)\in S$.

**Lemma 16.18.** If there is a P-selective language $S$ and $\mathrm{SAT}\le_m^p S$,
then $\mathrm{SAT}\in\mathrm{P}$, therefore $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $f$ be the polynomial reduction of SAT to $S$ and $s$ be the selector for $S$.
For the formula $\varphi$ we fix the variables sequentially. At step $i$ we build
$\varphi_0=\varphi\upharpoonright(x_i=0)$ and $\varphi_1=\varphi\upharpoonright(x_i=1)$,
calculate $f(\varphi_0), f(\varphi_1)$ and take
$$w:=s(f(\varphi_0), f(\varphi_1)).$$
If $w=f(\varphi_0)$, set $x_i:=0$, otherwise $x_i:=1$ (if both are equal, the choice is not important).
If $\varphi$ is satisfiable, then at least one of $\varphi_0,\varphi_1$ is satisfiable,
this means that the corresponding image lies in $S$, and the selector selects an executable branch.
By induction, after all the steps, we obtain a satisfying assignment, which we check.
If $\varphi$ is not satisfiable, any branch will result in a false assignment and the check will fail.
Time is polynomial. This means $\mathrm{SAT}\in\mathrm{P}$ and $\mathrm{P}=\mathrm{NP}$. $\square$

**Counterexample to gain.** P-selective by itself does not mean difficulty.
For example, the language $L=\{x: x_1=1\}$ is in $\mathrm{P}$ and P-selective,
but not NP-hard (if $\mathrm{P}\ne\mathrm{NP}$).

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.19. Research step: SAT to coRP => NP = coNP

**Question ("What if...?").** What if SAT is solved in coRP - should $\mathrm{NP}=\mathrm{coNP}$?

**Definition (coRP).** Language $L\in\mathrm{coRP}$ if there is a probabilistic
polynomial machine $A$, which for all $x$:
$$x\in L\Rightarrow \Pr[A(x)=1]=1,\quad x\notin L\Rightarrow \Pr[A(x)=1]\le 1/2.$$

**Lemma 16.19.** If $\mathrm{SAT}\in\mathrm{coRP}$, then $\mathrm{NP}=\mathrm{coNP}$.

*Proof.* (1) $\mathrm{coRP}\subseteq\mathrm{coNP}$: if $L\in\mathrm{coRP}$,
then $\overline{L}\in\mathrm{RP}$, and $\mathrm{RP}\subseteq\mathrm{NP}$ (guess random bits).
So $L\in\mathrm{coNP}$.

(2) coRP is closed under deterministic $\le_m^p$-reductions: if $L\le_m^p A$ and
$A\in\mathrm{coRP}$, then the algorithm for $A$ at input $f(x)$ gives the correct coRP
procedure for $L$.

Since SAT is NP-complete, from $\mathrm{SAT}\in\mathrm{coRP}$ we obtain
$\mathrm{NP}\subseteq\mathrm{coRP}\subseteq\mathrm{coNP}$, means $\mathrm{NP}=\mathrm{coNP}$. $\square$

**Counterexample to amplification.** coRP by itself does not mean NP-hard.
For example, the language $\Sigma^*$ lies in $\mathrm{coRP}\cap\mathrm{P}$ and cannot be
NP-hard in $\le_m^p$, otherwise $\mathrm{P}=\mathrm{NP}$ would follow.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.20. Exploratory Step: Accurately Counting SAT Solutions

**Question ("What if...?").** What if #SAT is computable in polynomial time?

**Definition (#SAT).** For a CNF formula $\varphi$, the function $\#\mathrm{SAT}(\varphi)$
equal to the number of satisfying assignments.

**Lemma 16.20.** If $\#\mathrm{SAT}$ is computable in polynomial time,
then $\mathrm{SAT}\in\mathrm{P}$, therefore $\mathrm{P}=\mathrm{NP}$.

*Proof.* At the input of the formula $\varphi$ we calculate $\#\mathrm{SAT}(\varphi)$.
If the value is greater than zero, then $\varphi$ is feasible, otherwise it is not.
This solves SAT in polynomial time, so $\mathrm{P}=\mathrm{NP}$. $\square$

**Counterexample to gain.** It is impossible to replace exact counting with modulo 2 counting.
Formula
$$\psi=(x_1\lor x_2)\land(\neg x_1\lor \neg x_2)$$
has exactly 2 solutions (parity 0), and the formula
$$\theta=(x_1\land\neg x_1)$$
has 0 solutions (parity 0). Therefore, knowledge of $\#\mathrm{SAT}(\cdot)\bmod 2$
does not allow you to solve SAT in the general case.

**Barrier check.**
- *Relativization:* yes (argument - direct calculation of the number of solutions).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.21. Exploratory step: FPRAS for #SAT

**Question ("What if...?").** What if there was an FPRAS for #SAT?

**Definition (FPRAS for #SAT).** Randomized Algorithm $A$ - FPRAS for
$\#\mathrm{SAT}$ if for any formula $\varphi$, parameters $\varepsilon\in(0,1)$ and
$\delta\in(0,1)$ it works for $\mathrm{poly}(|\varphi|,1/\varepsilon,\log(1/\delta))$ and
with probability $\ge 1-\delta$ returns a number $\widetilde{N}$ such that
$$ (1-\varepsilon)\#\mathrm{SAT}(\varphi)\le \widetilde{N}\le (1+\varepsilon)\#\mathrm{SAT}(\varphi). $$

**Lemma 16.21.** If there is an FPRAS for $\#\mathrm{SAT}$, then $\mathrm{SAT}\in\mathrm{RP}$,
hence $\mathrm{NP}=\mathrm{RP}$.

*Proof.* Use self-reduction search (step 16.3), replacing SAT calls
on FPRAS for $\#\mathrm{SAT}$.

Let $\varphi$ be over $n$ variables. For $i=1..n$ consider
$\varphi_0:=\varphi\upharpoonright(x_i=0)$ and $\varphi_1:=\varphi\upharpoonright(x_i=1)$ and
Let's run FPRAS on both formulas with $\varepsilon=1/2$ and $\delta:=1/(10n)$. If both scores are 0,
reject; otherwise, we select the branch with a non-zero score and continue. At the end we get the assignment $a$
and deterministically check $\varphi(a)=1$; We accept it if and only if the check passes.

If $\varphi$ is unsatisfiable, then the test will never pass, so we always reject.
If $\varphi$ is satisfiable, then successful calls to FPRAS result in a score of zero if and only if
when the corresponding branch has 0 solutions, so we can always choose a branch with at least one solution
and reach a satisfying $a$. By joint probability, all $2n$ calls are successful with probability
$\ge 1-2n\delta\ge 4/5$, which means we accept with probability $\ge 1/2$.
So, $\mathrm{SAT}\in\mathrm{RP}$, and by Lemma 16.14 $\mathrm{NP}=\mathrm{RP}$. $\square$

**Counterexample to gain.** Knowing $\#\mathrm{SAT}(\varphi)\bmod 2$ does not solve SAT
(see counterexample in step 16.20), means "approximation" without guarantee
multiplicative precision may not be sufficient.

**Barrier check.**
- *Relativization:* yes (the argument is combinatorial and transfers to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.22. Research Step: SAT to ZPP => NP = ZPP

**Question ("What if...?").** What if SAT is solved in ZPP - does the equality follow $\mathrm{NP}=\mathrm{ZPP}$?

**Definition (ZPP).** $\mathrm{ZPP}=\mathrm{RP}\cap\mathrm{coRP}$; equivalent,
is a class of languages recognized by randomized expected algorithms
polynomial time without errors (Las Vegas).

**Lemma 16.22.** If $\mathrm{SAT}\in\mathrm{ZPP}$, then $\mathrm{NP}=\mathrm{ZPP}$.

*Proof.* Since SAT is NP-complete and ZPP is closed in deterministic
$\le_m^p$-reductions, from $\mathrm{SAT}\in\mathrm{ZPP}$ it follows
$\mathrm{NP}\subseteq\mathrm{ZPP}$. On the other hand, $\mathrm{ZPP}\subseteq\mathrm{RP}\subseteq\mathrm{NP}$.
Therefore, $\mathrm{NP}=\mathrm{ZPP}$. $\square$

**Conclusion/failure.** The equality $\mathrm{NP}=\mathrm{ZPP}$ by itself does not give
$\mathrm{P}=\mathrm{NP}$ without derandomization $\mathrm{ZPP}=\mathrm{P}$.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.23. Exploratory step: SAT almost everywhere in P

**Question ("What if...?").** What if SAT is solved in polynomial time for all sufficiently large input lengths?

**Definition (a.e.-P).** A language $L$ is called *almost everywhere* in $\mathrm{P}$ if
there is $n_0$ and a polynomial algorithm $A$ such that for all $x$ with $|x|\ge n_0$:
$A(x)$ decides the membership of $x\in L$.

**Lemma 16.23.** If SAT is almost everywhere in $\mathrm{P}$, then $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $A$ be correct for all lengths $\ge n_0$.
For lengths $<n_0$, we calculate the answers in advance (this is a finite set of strings) and
let's sew them into the algorithm. Then we get a polynomial algorithm that solves SAT on all inputs.
Therefore, $\mathrm{SAT}\in\mathrm{P}$ and $\mathrm{P}=\mathrm{NP}$. $\square$

**Counterexample to strengthening.** The condition "in $\mathrm{P}$ on an infinite number of lengths" is not sufficient.
Let $H\in\mathrm{DTIME}(2^n)\setminus\mathrm{P}$ (exists by the time hierarchy theorem).
Let's define
$$L:=\{z:\ |z|\ \text{even}\}\ \cup\ \{1^{|x|}0x:\ x\in H\}.$$
Then $L$ is trivial on all even lengths (meaning "light" on infinitely many lengths),
but $H\le_m^p L$ by reduction $x\mapsto 1^{|x|}0x$ (length $2|x|+1$), so from $L\in\mathrm{P}$
$H\in\mathrm{P}$ would follow--a contradiction. This means that the condition "at infinitely many lengths" does not give $\mathrm{P}$.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.24. Exploratory step: SAT to RP with O(log n) random bits

**Question ("What if...?")** What if SAT is solved in RP using only $O(\log n)$ random bits?

**Definition (RP$_{\log}$).** Language $L\in\mathrm{RP}_{\log}$, if there is an RP machine,
which uses at most $c\log n$ random bits on inputs of length $n$.

**Lemma 16.24.** If $\mathrm{SAT}\in\mathrm{RP}_{\log}$, then $\mathrm{SAT}\in\mathrm{P}$,
hence $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $A$ be an RP algorithm for SAT with $m(n)\le c\log n$ random bits.
For an input $\varphi$ of length $n$, we go through all $2^{m(n)}\le n^c$ random strings $r$ and
let's run $A(\varphi,r)$.
If $\varphi$ is unsatisfiable, then $A$ never accepts, so we reject.
If $\varphi$ is satisfiable and there is at least one $r$ with acceptance, then we accept.
Time is polynomial. $\square$

**Counterexample to strengthening.** For $m(n)=\Theta(n)$ full search of random strings
takes $2^{\Theta(n)}$ time, so the argument does not carry over to the general RP.
Therefore, the $O(\log n)$ constraint is essential.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.25. Exploratory step: NP-complete language in io-P

**Question ("What if...?").** If an NP-complete language is solved in polynomial time
on infinitely many input lengths, does $\mathrm{P}=\mathrm{NP}$?

**Definition (io-P).** A language $L$ belongs to io-P if there is a polynomial
algorithm $A$ and an infinite set of lengths $N\subseteq\mathbb{N}$, such that for all
$n\in N$ and all strings $x$ of length $n$ satisfy $A(x)=1\iff x\in L$.

**Lemma 16.25 (counterexample).** There is an NP-complete language $L'$ such that $L'\in$ io-P.

*Proof.* Let $p(n)=n^2$ and
$$L' = \{x0^{p(|x|)-|x|}: x\in\mathrm{SAT}\}.$$ 
Then any string from $L'$ has length $n^2$. Reduction $x\mapsto x0^{n^2-n}$
is polynomial, which means $L'$ is NP-complete. For any length $m$ that is not a square,
there are no strings in $L'$, so an algorithm that always rejects at such lengths
solves $L'$ in polynomial time. There are infinitely many non-square lengths, which means
$L'\in$ io-P. Hence the condition "NP-complete and light on infinitely many lengths"
does not imply $\mathrm{P}=\mathrm{NP}$. $\square$

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.26. Exploratory step: NP-full language is easy at density 1 length

**Question ("What if...?").** If an NP-complete language is solved in polynomial time
on the set of lengths of density 1, does $\mathrm{P}=\mathrm{NP}$?

**Definition (density 1 over lengths).** The set of lengths $N\subseteq\mathbb{N}$ has
density 1 if
$$\lim_{m\to\infty} \frac{|N\cap\{1,\dots,m\}|}{m}=1.$$
A language $L$ is said to be *easy on lengths of $N$* if there exists a polynomial
algorithm $A$, correct for all strings $x$ with $|x|\in N$.

**Lemma 16.26 (counterexample).** There is an NP-complete language $L'$ and a set of lengths $N$
density 1 such that $L'$ is light on lengths of $N$.

*Proof.* Set $p(n)=n^2$ and
$$L' = \{x0^{p(|x|)-|x|}: x\in\mathrm{SAT}\}.$$
The reduction $x\mapsto x0^{n^2-n}$ is polynomial, which means $L'$ is NP-complete.
Any string from $L'$ has length square; at lengths that are not squares,
$L'$ is empty, and the always rejecting algorithm is correct. Let $N$ be a set
non-square lengths. Then $|N\cap\{1,\dots,m\}|=m-\lfloor\sqrt{m}\rfloor$, so
$N$ has density 1. Hence $L'$ is light on lengths of $N$. $\square$

**Conclusion/failure.** The property "NP-full language is light at density 1 length" is too weak:
it is already achieved by a simple padding construction and does not lead to $\mathrm{P}=\mathrm{NP}$
no additional ideas.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.27. Research step: SAT to BPP => SAT to P/poly

**Question ("What if...?").** If SAT is decided in BPP, does it follow that
existence of polynomial circuits?

**Lemma 16.27 (Adleman).** If $\mathrm{SAT}\in\mathrm{BPP}$ then $\mathrm{SAT}\in\mathrm{P/poly}$.

*Proof.* Let $A$ be a BPP algorithm for SAT using $m(n)$ random bits.
Let's strengthen it by repeating it until the error $\varepsilon=2^{-2n}$, obtaining the algorithm $A'$
(time and number of bits remain polynomial).
For a fixed length $n$, let $B_x$ denote the set of random strings $r$
lengths $m(n)$ on which $A'(x,r)$ is wrong. Then $|B_x|\le \varepsilon 2^{m(n)}$.
The union over all $x\in\{0,1\}^n$ has the size
$$\left|\bigcup_{x} B_x\right|\le 2^n\cdot \varepsilon 2^{m(n)}<2^{m(n)},$$
therefore there is a string $r_n$ on which $A'$ is valid for all inputs of length $n$.
By hard-wiring $r_n$ into the circuit, we obtain a family of circuits of polynomial size,
decisive SAT on every length $n$. So $\mathrm{SAT}\in\mathrm{P/poly}$. $\square$

**Conclusion/failure.** From SAT $\in\mathrm{BPP}$ only unevenness follows
($\mathrm{SAT}\in\mathrm{P/poly}$) and, according to Karp-Lipton, PH collapse to $\Sigma_2^p$;
this does not give $\mathrm{P}=\mathrm{NP}$ without additional ideas about uniformity.

**Barrier check.**
- *Relativization:* yes (the argument is transferred to oracles).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.28. Research step: NP  AC^0?

**Question ("What if...?").** What if all $\mathrm{NP}$ lies in $\mathrm{AC}^0$?

**Lemma 16.28 (counterexample).** $\mathrm{NP}\not\subseteq\mathrm{AC}^0$.

*Proof.* The function $\mathrm{PARITY}$ belongs to $\mathrm{P}\subseteq\mathrm{NP}$.
By Section 11.3, $\mathrm{PARITY}\notin\mathrm{AC}^0$.
This means there is a language from $\mathrm{NP}$ that does not lie in $\mathrm{AC}^0$, that is
$\mathrm{NP}\not\subseteq\mathrm{AC}^0$. $\square$

**Conclusion/failure.** The statement $\mathrm{NP}\subseteq\mathrm{AC}^0$ is too strong:
it is already refuted by classical lower bounds for $\mathrm{AC}^0$.

**Barrier check.**
- *Relativization:* not applicable (statement about uneven patterns).
- *Natural proofs:* does not interfere; lower bounds for $\mathrm{AC}^0$ are known.
- *Algebrization:* not applicable.

### 16.29. Exploratory step: average ease of NP-complete language

**Question ("What if...?").** If an NP-complete language is solved polynomially
on almost all inputs of each length (uniformly across $\{0,1\}^n$), does $\mathrm{P}=\mathrm{NP}$ follow?

**Definition (error on length $n$).** Algorithm $A$ has error $\varepsilon(n)$ in language $L$,
if $\Pr_{x\in\{0,1\}^n}[A(x)\ne L(x)]\le \varepsilon(n)$.

**Lemma 16.29 (counterexample).** There is an NP-complete language $L'$ and a polynomial algorithm $A$,
for which the error on length $n$ does not exceed $2^{-\Omega(n)}$.

*Proof.* Take $p(m)=m^2$ and define
$$L' = \{x0^{p(|x|)} : x\in\mathrm{SAT}\}.$$
The reduction $x\mapsto x0^{p(|x|)}$ is polynomial, which means $L'$ is NP-complete.
If the length of $n$ has the form $n=m+p(m)=m+m^2$, then $\{0,1\}^n$ contains at most $2^m$ rows from $L'$,
therefore, the share of recipients does not exceed $2^m/2^{m+m^2}=2^{-m^2}=2^{-\Theta(n)}$.
If the length $n$ is not of this form, then $L'\cap\{0,1\}^n=\varnothing$.
Algorithm $A$, always rejecting, has an error of at most $2^{-\Theta(n)}$ on each length.
$\square$

**Output/failure.** Having an NP-complete language that is light on almost all inputs of every length,
does not imply $\mathrm{P}=\mathrm{NP}$: this is achieved by simple padding.

**Barrier check.**
- *Relativization:* yes (padding and share estimation are preserved with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

### 16.30. Exploratory step: NP-complete language in subexponential time?

**Question ("What if...?").** If there is an NP-complete language that can be solved in
time $2^{n^\varepsilon}$ (for some $0<\varepsilon<1$), does $\mathrm{P}=\mathrm{NP}$ follow?

**Lemma 16.30 (counterexample).** There is an NP-complete language $L'$ in
$\mathrm{DTIME}(2^{O(\sqrt{n})})$ (that is, in sub-exponential time).

*Proof.* Define
$$L' = \{x0^{|x|^2-|x|} : x\in\mathrm{SAT}\}.$$
The reduction $x\mapsto x0^{|x|^2-|x|}$ is polynomial, which means $L'$ is NP-complete.
For an input of length $n$, check whether $n$ is a square of $m^2$ and that the last
$n-m$ bits are zero; otherwise we reject. If $n=m^2$, take the first $m$ bits as $x$
and solve SAT by exhaustive search for $2^{O(m)}=2^{O(\sqrt{n})}$.
Therefore, $L'\in\mathrm{DTIME}(2^{O(\sqrt{n})})$. $\square$

**Conclusion/failure.** Having an NP-complete language in sub-exponential time
does not imply $\mathrm{P}=\mathrm{NP}$: this is achieved by padding.

**Barrier check.**
- *Relativization:* yes (padding is preserved with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

### 16.31. Research step: p-bounded proof system?

**Question ("What if...?").** What if there is a polynomial bounded
propositional evidence system?

**Definition (p-bounded).** Proof system $P$ (in the sense of Cook-Reckhow)
p-bounded if there is a polynomial $p$ such that every tautology $\varphi$
has $P$-proof of length $\le p(|\varphi|)$.

**Lemma 16.31.** If there is a p-bounded proof system, then
$\mathrm{NP}=\mathrm{coNP}$.

*Proof.* Let $P$ be p-bounded. NP machine based on input $\varphi$
guesses a string of length $\le p(|\varphi|)$ and checks that it is correct
$P$-proof $\varphi$ (the test is polynomial by definition of the proof system).
So $\mathrm{TAUT}\in\mathrm{NP}$. Since $\mathrm{TAUT}$ is coNP-complete,
we get $\mathrm{coNP}\subseteq\mathrm{NP}$, and therefore
$\mathrm{NP}=\mathrm{coNP}$. $\square$

**Conclusion/failure.** p-boundedness: extremely strong requirement:
it immediately entails the collapse of $\mathrm{NP}$ and $\mathrm{coNP}$.

**Barrier check.**
- *Relativization:* not applicable (statement about proof systems).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.32. Exploratory step: SAT in BPP with O(log n) random bits

**Question ("What if...?").** What if SAT is solved in BPP using only
$O(\log n)$ random bits?

**Definition (BPP$_{\log}$).** Language $L\in\mathrm{BPP}_{\log}$, if exists
BPP algorithm using at most $c\log n$ random bits on inputs of length $n$.

**Lemma 16.32.** If $\mathrm{SAT}\in\mathrm{BPP}_{\log}$, then $\mathrm{SAT}\in\mathrm{P}$,
hence $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let $A$ be a BPP algorithm for SAT using $m(n)\le c\log n$
random bits. For a formula $\varphi$ of length $n$, consider all $2^{m(n)}\le n^c$
random strings $r$ and calculate the acceptance rate $A(\varphi,r)$.
If $\varphi$ is satisfiable, this fraction is $\ge 2/3$, otherwise $\le 1/3$.
Comparison with the $1/2$ threshold gives a deterministic solution in polynomial time.
$\square$

**Counterexample to strengthening.** For $m(n)=\Theta(n)$ full search of random strings
takes $2^{\Theta(n)}$ time, so the argument does not carry over to the general BPP.

**Barrier check.**
- *Relativization:* yes (random string search is saved with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

### 16.33. Exploratory Step: Is the SAT Sparse?

**Question ("What if...?").** Can the SAT be a sparse language?

**Definition (sparse).** A language $L$ is sparse if there exists a polynomial $p$ such that
$|L\cap\Sigma^{\le n}|\le p(n)$ for all $n$.

**Lemma 16.33 (counterexample).** SAT is not a sparse language.

*Proof.* For each $m$ and each assignment $a\in\{0,1\}^m$ consider the formula
$$\varphi_a:=\bigwedge_{i=1}^m \ell_i,$$
where $\ell_i=x_i$ for $a_i=1$ and $\ell_i=\neg x_i$ for $a_i=0$.
Each $\varphi_a$ is satisfiable (uniquely) and has length $\mathrm{poly}(m)$
(with any standard input coding).
The formulas $\varphi_a$ are different, so among the strings of length $\le \mathrm{poly}(m)$ there are at least $2^m$
feasible formulas. Since $2^m$ outgrows any polynomial in $\mathrm{poly}(m)$,
SAT is not sparse. $\square$

**Conclusion/failure.** Trying to use SAT sparsity as a path to $\mathrm{P}\ne\mathrm{NP}$
breaks off at a rudimentary score: the SAT is too dense.

**Barrier check.**
- *Relativization:* not applicable (fixed language statement).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.34. Research Step: SAT with Logarithmic Certificates

**Question ("What if...?").** If SAT has certificates of length $O(\log n)$,
should $\mathrm{P}=\mathrm{NP}$?

**Definition (NP$_{\log}$).** Language $L\in\mathrm{NP}_{\log}$, if exists
a polynomial verifier $V(x,y)$ and a constant $c$ such that for all $x$:
$$x\in L\iff \exists y\in\{0,1\}^{\le c\log|x|}: V(x,y)=1.$$

**Lemma 16.34.** If $\mathrm{SAT}\in\mathrm{NP}_{\log}$, then $\mathrm{SAT}\in\mathrm{P}$,
hence $\mathrm{P}=\mathrm{NP}$.

*Proof.* Let there be a verifier for SAT with a length certificate
at most $c\log n$. Then, at an input of length $n$, we can enumerate all
$2^{c\log n}=n^c$ certificates $y$ and check $V(x,y)$.
This is deterministic polynomial time. $\square$

**Counterexample to the gain.** With a certificate length of $\Theta(n)$, exhaustive search
requires $2^{\Theta(n)}$ time, so the argument does not carry over to the general NP.

**Barrier check.**
- *Relativization:* yes (certificate enumeration is saved with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

### 16.35. Exploratory step: one-way functions

**Question ("What if...?").** What if there are one-way functions?

**Definition (OWF).** The function $f:\{0,1\}^*\to\{0,1\}^*$ is one-way if
there is a polynomial computable family $f_n:\{0,1\}^n\to\{0,1\}^{\mathrm{poly}(n)}$,
such that for any polynomial algorithm $A$ the probability
$$\Pr_{x\leftarrow\{0,1\}^n}\bigl[f_n(A(1^n,f_n(x)))=f_n(x)\bigr]$$
negligible.

**Lemma 16.35.** If OWFs exist, then $\mathrm{P}\ne\mathrm{NP}$.

*Proof.* Assume that $\mathrm{P}=\mathrm{NP}$. Let's fix it
polynomial computable OWF $f_n$. For a given $n$ and $y$ we will restore bit by bit
preimage $x\in\{0,1\}^n$: at step $i$ we check whether there is a string $x$ of length $n$ with the given prefix
length $i$ such that $f_n(x)=y$. This is an NP question, which means that for $\mathrm{P}=\mathrm{NP}$ it is solved in $\mathrm{poly}(n)$.
After $n$ steps we get $x$ with $f_n(x)=y$. Therefore, $f_n$ is invertible in polynomial time,
the contradiction of one-sidedness. This means that the existence of OWF implies $\mathrm{P}\ne\mathrm{NP}$. $\square$

**Conclusion/failure.** Proving the existence of OWF is sufficient for $\mathrm{P}\ne\mathrm{NP}$,
but this is no simpler than the original problem.

**Barrier check.**
- *Relativization:* yes (the argument is preserved with the oracle).
- *Natural proofs:* not applicable.
- *Algebrization:* not applicable.

### 16.36. Exploratory step: PRG with logarithmic seed

**Question ("What if...?").** What if there is a PRG with a seed of length $O(\log n)$,
which fools all BPP algorithms?

**Definition (PRG for BPP).** Family $g_n:\{0,1\}^{s(n)}\to\{0,1\}^{m(n)}$
with $s(n)=O(\log n)$ and $m(n)=\mathrm{poly}(n)$, computable in polynomial time,
such that for any polynomial algorithm $A$ and all $n$:
$$\left|\Pr[A(g_n(U_{s(n)}))=1]-\Pr[A(U_{m(n)})=1]\right|\le 1/10.$$

**Lemma 16.36.** If such a PRG exists, then $\mathrm{BPP}=\mathrm{P}$.

*Proof.* Let $L\in\mathrm{BPP}$ and $A$ be its probabilistic polynomial
algorithm with $m(n)$ random bits and error $\le 1/3$.
For an input $x$ of length $n$, let's go through all $2^{s(n)}=\mathrm{poly}(n)$ seeds $r$,
Let's calculate the acceptance rate $A(x,g_n(r))$ and compare it with the threshold $1/2$.
Since PRG preserves the probability with an accuracy of $1/10$, then for $x\in L$ the average
$\ge 2/3-1/10>1/2$, and for $x\notin L$ the average is $\le 1/3+1/10<1/2$.
We obtain a deterministic polynomial algorithm. $\square$

**Counterexample to gain.** If $s(n)=\Theta(n)$, then complete search of seeds
takes $2^{\Theta(n)}$ time and the proof does not work.

**Barrier check.**
- *Relativization:* yes (seed search is saved with the oracle).
- *Natural proofs:* not applicable (not about schematic lower bounds).
- *Algebrization:* not applicable.

-/
