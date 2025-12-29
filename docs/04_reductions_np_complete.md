## 4. Reductions and NPcompleteness (minimal apparatus)

**Definition (polynomial many-one reduction).** The language $A$ *reduces* to $B$
(notation $A\le_m^p B$), if there is a polynomial computable function
$f$ such that for all $x$:
$$x\in A \iff f(x)\in B.$$

**Lean-skeleton:** definitions of many-one reduction and NP-completeness are included in `formal/PvNP/Core/Reductions.lean`.

**Definition (NP-complete).** A language $B$ is NP-complete if (i) $B\in\mathrm{NP}$ and (ii) for any $A\in\mathrm{NP}$ $A\le_m^p B$ is true.

**Lemma 4.1.** $\mathrm{SAT}\in\mathrm{NP}$.

*Proof.* Certificate - assignment of Boolean variables.
The verifier substitutes it into the formula in polynomial time and checks that
that every clause is true. $\square$

**Theorem 4.2 (Cook-Levin).** SAT is NPcomplete.

*Proof.* Let $L\in\mathrm{NP}$.
According to the certificate formulation (Section 2), there is a polynomial $p$
and a deterministic polynomial verifier $V$ such that
$$x\in L \iff \exists y\in\{0,1\}^{p(|x|)}:\ V(x,y)=1.$$

Let us fix a deterministic single-band MT $M$ that calculates $V$ (the robustness of the model).
For an input $x$ of length $n$, machine $M$ stops in at most $T(n)$ steps on all lines $\langle x,y\rangle$ (where $|y|=p(n)$).
Let's replace $T(n)$ with $T(n)+n+p(n)+2$ so that there is enough space for the entrance; let's supplement $M$ with idle steps so that it takes **exactly** $T:=T(n)$ steps.

Let us construct, from $x$, a CNF formula $\varphi_x$, satisfiable if and only if
when there exists a certificate $y$ such that $M$ accepts $\langle x,y\rangle$.

**Variables.** Let $\Gamma$ be the alphabet of the tape $M$ (including $0,1,\square,\#,\triangleright$).
$Q$ is a set of states; $q_0$ is the starting one, $q_{\mathrm{acc}}$ is the receiving one.
Consider the extended alphabet $\Gamma':=\Gamma\cup(Q\times\Gamma)$:
the symbol $(q,a)$ means that the head is in a cage, the machine is in state $q$,
and "under the head" is written $a$.

Let us set $W:=T+2$ and consider the cells $i\in\{0,1,\dots,W\}$ (the outermost ones are the boundaries).
For each $t\in\{0,1,\dots,T\}$, $i\in\{0,1,\dots,W\}$ and $s\in\Gamma'$
introduce the variable $X_{t,i,s}$: "at moment $t$, the symbol $s$ is written in cell $i$."

**Clauses (CNF).** The formula $\varphi_x$ is the conjunction of the following families.

(A) *(Exactly one character per cell.)* For each $(t,i)$:
- "at least one" : $\bigvee_{s\in\Gamma'} X_{t,i,s}$;
- "no more than one": for all $s\ne s'$ we add $(\neg X_{t,i,s}\lor\neg X_{t,i,s'})$.

(B) *(Exactly one head position/state.)* For each $t$ we require that exactly one cell contains a "state" symbol:
- $\bigvee_{i\in\{1,\dots,W-1\},\ q\in Q,\ a\in\Gamma} X_{t,i,(q,a)}$;
- pairwise prohibitions for different triples $(i,q,a)$.

(C) *(Boundaries and initial configuration.)* For all $t$ we fix the boundaries: $X_{t,0,\triangleright}$ and $X_{t,W,\square}$.
Let $x=x_1\dots x_n$. At moment $0$ we define a tape of the form $\triangleright\ x\ \#\ y\ \square\cdots$ and the starting state in the first letter $x$:
- $X_{0,1,(q_0,x_1)}$;
- for $i=2,\dots,n$ : $X_{0,i,x_i}$;
- $X_{0,n+1,\#}$;
- for the "certificate zone" $i=n+2,\dots,n+1+p(n)$ : add $(X_{0,i,0}\lor X_{0,i,1})$;
- for the remaining $i>n+1+p(n)$ we fix $X_{0,i,\square}$.

(D) *(One computation step, local restrictions.)* For each $t<T$
and $i\in\{1,\dots,W-1\}$ we require coordination of the window $3\times 2$ with the transition $\delta$.
Formally: consider all 6 triplets of symbols
$$(a_{-1},a_0,a_{+1};\ b_{-1},b_0,b_{+1})\in(\Gamma')^6,$$
who **cannot** meet like
$$(\text{symbols in }(t,i-1),(t,i),(t,i+1);\ \text{symbols in }(t+1,i-1),(t+1,i),(t+1,i+1))$$
in the correct move $M$. For each such 6-triple, we add a clause prohibiting its appearance:
$$(
eg X_{t,i-1,a_{-1}}\lor
eg X_{t,i,a_0}\lor
eg X_{t,i+1,a_{+1}}\lor
eg X_{t+1,i-1,b_{-1}}\lor
eg X_{t+1,i,b_0}\lor
eg X_{t+1,i+1,b_{+1}}).$$
Since $M$ is fixed, $|\Gamma'|$ is a constant, so the number of local patterns is a constant; total clause (D) $O(T\cdot W)=O(T^2)$.
$$(a_{-1},a_0,a_{+1};\ b_{-1},b_0,b_{+1})\in(\Gamma')^6,$$
who **cannot** meet like
$$(\text{symbols in }(t,i-1),(t,i),(t,i+1);\ \text{symbols in }(t+1,i-1),(t+1,i),(t+1,i+1))$$
in the correct move $M$. For each such forbidden 6-triple, we add one CNF clause that prohibits its simultaneous occurrence:
$$(
\neg X_{t,i-1,a_{-1}}\lor\neg X_{t,i,a_0}\lor\neg X_{t,i+1,a_{+1}}\lor
\neg X_{t+1,i-1,b_{-1}}\lor\neg X_{t+1,i,b_0}\lor\neg X_{t+1,i+1,b_{+1}}).$$

(E) *(Acceptance.)* We require that at step $T$ the machine be in the receiving state:
$$\bigvee_{i\in\{1,\dots,W-1\},\ a\in\Gamma} X_{T,i,(q_{\mathrm{acc}},a)}.$$

**Size estimate.** The number of variables is $|\{X_{t,i,s}\}|=(T+1)(W+1)|\Gamma'|=O(T^2)$, and the number of clauses is also $O(T^2)$.
This means $x\mapsto\varphi_x$ is calculated using $\mathrm{poly}(|x|)$.

**Correctness.**
- If $x\in L$, then there exists $y$ such that $M$ takes $\langle x,y\rangle$.
  The length calculation table $T$ specifies the values $X_{t,i,s}$; by construction, (A)-(E) are satisfied, which means $\varphi_x$ is satisfiable.
- If $\varphi_x$ is satisfiable, then from (A), (B) we obtain the correct encoding of "exactly one character" and "exactly one head/state".
  (C) commits input $x$ and sets certificate $y$ in the allocated zone, (D) coordinates neighboring clocks with $\delta$.
  This means that the variables describe the calculation of $M$ on $\langle x,y\rangle$, and by (E) it is accepting; means $x\in L$.

So, for any $L\in\mathrm{NP}$ we have $L\le_m^p\mathrm{SAT}$,
that is, the SAT is NP-hard. Together with Lemma 4.1 we obtain that SAT is NP-complete.
$\square$

Below is the complete reduction of SAT $\le_m^p$ 3SAT.
