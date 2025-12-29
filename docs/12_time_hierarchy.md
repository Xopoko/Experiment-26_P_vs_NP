## 12. Time hierarchy: diagonalization (complete proof)

This section is needed as a "calibration": we will prove a rigorous result on the separation
classes in time and we will clearly see that the proof **relativizes**
(Baker-Gill-Solovay barrier).

**Definition (time-constructible).** Function $t:\mathbb{N}\to\mathbb{N}$
is called *time-constructible* if there is a deterministic MT $T$
such that at input $1^n$ it stops exactly after $t(n)$ steps
(or, equivalently, can write $t(n)$ in unary form in $O(t(n))$ time).

**Lemma 12.1 (universal simulation, cited).** There is a universal
deterministic multi-tape MT $U$, which by input $(\langle M\rangle, x, 1^s)$
simulates the operation of a deterministic MT $M$ for $x$ for $s$ steps
and stops in $O(s\log_2 s)$ steps.
See `../resources/downloads/uw_hierarchy_2022_lecture5.pdf`.

*Comment.* This log factor is the standard price to pay for versatility
(transition coding, tape addressing, etc.). For hierarchy purposes it is acceptable.

**Definition (diagonal language).** Let us fix the encoding that each
the word $y\in\{0,1\}^*$ is associated with a deterministic MT $M_y$
(if $y$ is incorrect as code, we consider $M_y$ to be a machine that always rejects).

For time-constructible $t$ we define a language
$$L_t:=\{y:\ M_y(y)\ \text{does not take for}\ \le t(|y|)\ \text{steps}\}.$$

**Theorem 12.2 (Deterministic Time Hierarchy).** Let $t(n)\ge n$ be
time-constructible. Then
$$\mathrm{TIME}(t(n))\subsetneq\mathrm{TIME}(t(n)\log_2 t(n)).$$

*Proof.*

1) Let us show that $L_t\in\mathrm{TIME}(t(n)\log_2 t(n))$.
Algorithm $A$ on input $y$ of length $n$:

- using a "clock" machine (which exists according to time-constructible) we obtain the limit $t(n)$;
- launch the universal simulation $U(\langle M_y\rangle, y, 1^{t(n)})$;
- if the simulation detects taking $\le t(n)$ steps, we reject, otherwise we accept.

By Lemma 12.1, the simulation takes $O(t(n)\log_2 t(n))$ time;
the rest of the work is dominated by less, which means $A$ fits into
$O(t(n)\log_2 t(n))$.

2) Let us show that $L_t\notin\mathrm{TIME}(t(n))$. Let's assume the opposite:
there is a deterministic MT $D$ that solves $L_t$ in $\le t(n)$ steps
on inputs of length $n$.

Consider the input $y:=\langle D\rangle$ (the code of $D$ itself).
Since $D$ solves $L_t$, we have:

- if $D(y)$ accepts, then $y\in L_t$, that is, by definition
  $M_y(y)=D(y)$ **doesn't** take $\le t(|y|)$ steps - a contradiction;
- if $D(y)$ rejects, then $y\notin L_t$, that is, $D(y)$ accepts
  in $\le t(|y|)$ steps--a contradiction.

Consequently, such $D$ does not exist and $L_t\notin\mathrm{TIME}(t(n))$.

The rigor of inclusion follows from (1) and (2). $\square$

**Remark 12.3 (relativization).** This proof carries over almost verbatim
to the oracle world: for any oracle $A$ is true
$\mathrm{TIME}^A(t)\subsetneq\mathrm{TIME}^A(t\log_2 t)$.
Therefore it cannot directly solve $\mathrm{P}$ vs $\mathrm{NP}$
due to the existence of oracles $A,B$ with opposite answers.

**Corollary 12.4.** $\mathrm{P}\subsetneq\mathrm{EXP}$.

*Proof.* First note that $\mathrm{P}\subseteq\mathrm{TIME}(2^n)$:
any function $n^k$ ultimately does not exceed $2^n$, which means
$\bigcup_k\mathrm{TIME}(n^k)\subseteq\mathrm{TIME}(2^n)$.

Let's apply Theorem 12.2 to $t(n)=2^n$ (it is time-constructible).
We get the language $L\in\mathrm{TIME}(2^n\cdot n)\setminus\mathrm{TIME}(2^n)$.
Then $L\notin\mathrm{P}$, since $\mathrm{P}\subseteq\mathrm{TIME}(2^n)$.
In this case, $\mathrm{TIME}(2^n\cdot n)\subseteq\mathrm{EXP}$.
So $\mathrm{P}\subsetneq\mathrm{EXP}$. $\square$
