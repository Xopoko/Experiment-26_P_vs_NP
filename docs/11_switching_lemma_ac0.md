## 11. From depth 2 to AC0: switching lemma (quoted) -> PARITY  AC0

The lower bound from Section 10 is for depth 2 (DNF/CNF).
For an arbitrary constant depth $d$, the key tool is Hustad's switching lemma.
Here we fix the formal "skeleton" of the proof: what definitions/lemmas are needed
and where the switching lemma is applied.

### 11.0. Constraints and decision trees

**Definition (constraint).** Constraint $\rho$ on variables $x_1,\dots,x_n$ --
is a vector of $\{0,1,*\}^n$.
The coordinate $\rho_i\in\{0,1\}$ means fixation $x_i=\rho_i$,
and $\rho_i=*\,$ means "free".
Let $m(\rho)$ denote the number of free variables.

For a Boolean function $f:\{0,1\}^n\to\{0,1\}$ the bounded function
$f\upharpoonright\rho$ is obtained by substituting fixed values
and is considered as a function of $m(\rho)$ free variables.

**Definition (decision tree).** Decision tree for $f$ is an adaptive algorithm,
which at the input $x$ sequentially requests the values of individual $x_i$
and in the sheet it gives 0/1.
*Depth*--the maximum number of requests on the root->leaf path.
Let us denote the minimum possible depth by $\mathrm{DT}(f)$.

**Fact 11.6.** If $\mathrm{DT}(f)\le d$, then $f$ has a DNF of width $\le d$ and a CNF of width $\le d$.

*Proof.* Take a decision tree of depth $d$ for $f$.
Each path leading to a leaf with value 1 defines a term
(conjunction of the requested literals) of length $\le d$;
The OR of all such terms evaluates $f$, giving a DNF of width $\le d$.
For CNF, apply the same argument to $\neg f$ and then de Morgan. $\square$

### 11.1. PARITY under restrictions (full proof)

**Lemma 11.3.** For any constraint $\rho$ the function
$\mathrm{PARITY}_n\upharpoonright\rho$ is equal to $\mathrm{PARITY}_{m(\rho)}$
or $\neg\mathrm{PARITY}_{m(\rho)}$ (that is, $\mathrm{PARITY}_{m(\rho)}\oplus c$
for some constant $c\in\{0,1\}$).

*Proof.* Parity is the XOR of all bits.
After substituting fixed variables, their contribution becomes constant
$c\in\{0,1\}$, and the remaining $m(\rho)$ free variables remain under XOR.
So $\mathrm{PARITY}_n\upharpoonright\rho = \mathrm{PARITY}_{m(\rho)}\oplus c$;
for $c=0$ this is parity, for $c=1$ it is its negation. $\square$

### 11.2. PARITY requires full decision-tree depth (full proof)

**Lemma 11.4.** $\mathrm{DT}(\mathrm{PARITY}_m)=m$.

*Proof.* The upper bound for $\le m$ is obvious: query all $m$ variables and compute XOR.

For the lower bound, we assume that there is a decision tree of depth $<m$,
calculating $\mathrm{PARITY}_m$. Then on any path to the sheet it is requested
$<m$ variables, which means there is at least one free variable left in the sheet.
But the sheet corresponds to the subcube specified by fixing the requested variables, and by
Lemma 10.1 parity on such a subcube cannot be constant, whereas
The decision tree in the sheet produces a constant. Contradiction. $\square$

**Corollary 11.5.** For any $\rho$ with $m(\rho)=m$ we have
$\mathrm{DT}(\mathrm{PARITY}_n\upharpoonright\rho)=m$
(in particular, if $m\ge 1$, then $\mathrm{PARITY}_n\upharpoonright\rho$ is not a constant).

*Proof.* By Lemma 11.3, the parity constraint is
$\mathrm{PARITY}_m$ or $\neg\mathrm{PARITY}_m$, and inverting the output does not change
decision-tree depth. We apply Lemma 11.4. $\square$

### 11.3. Switching lemma → PARITY $\notin$ AC⁰

Next we give the proof of Theorem 11.2, taking the switching lemma (Theorem 11.1).

**Theorem 11.1 (Hastad switching lemma, cited; form with explicit constants).**
Let $F$ be a DNF (or CNF) of width at most $w$ over $n$ variables.
Let $\rho$ be a random constraint chosen uniformly among the constraints
with exactly $s=\sigma n$ free variables, where $\sigma\le 1/5$.
Then for any $t\le s$
$$\Pr\big[\mathrm{DT}(F\upharpoonright\rho)>t\big] \le (10\sigma w)^t.$$

Source: O'Donnell, Lecture 14 (The Switching Lemma), Theorem 1.8; original result: Hastad (1986).

**Theorem 11.2 (PARITY $\notin$ AC0, proof of Theorem 11.1).**
For any fixed $k\ge 2$, any depth-$k$ AC0scheme,
computing $\mathrm{PARITY}_n$, has size $S\ge 2^{\Omega(n^{1/(k-1)})}$.

*Proof.* Let $C$ be a depth-$k$ circuit of size $S$ computing $\mathrm{PARITY}_n$.

1) *(Normalization, quoted.)* We can consider that the circuit is "layered"
(levels alternate AND/OR), inputs are literals, and fan-out is 1 (formula).
For a fixed $k$, this only increases the size to $S^{O(1)}$;
let us redesignate it again as $S$.

2) Set $w:=20\log_2 S$.
Next (also standard) we reduce to the case when the fan-in of all lower gates
does not exceed $w$; this is done by an additional random constraint, which
kills all lower gates of width $>w$ with positive probability
(O'Donnell, Lecture 14, end of proof of Theorem 3.1).
Let us again redesignate the resulting circuit as $C$.

3) Assume without loss of generality that the bottom layer is AND. Then each gate of the next layer calculates a DNF of width $\le w$.

Let's take $\sigma:=1/(20w)$ and apply a random constraint $\rho_1$
with exactly $\sigma n$ free variables. By Theorem 11.1
for a fixed such DNF the probability of the event is $\mathrm{DT}(\cdot)>w$
does not exceed $(10\sigma w)^w=(1/2)^w=S^{-20}$.

According to the union bound for all $\le S$ gates of this layer
there is a constraint $\rho_1$ such that *each* of them after the constraint
has $\mathrm{DT}\le w$. According to Fact 11.6, each such gate is equivalent
CNF of width $\le w$, and therefore two adjacent layers of the circuit become of the same type
and can be merged. As a result, we obtain a $k-1$ depth scheme with the same
restriction of fan-in $\le w$ at the lower level.

4) Repeat step (3) another $k-3$ times (each time leaving a fraction of $\sigma$
free variables). Let $\rho$ be the composition of the obtained constraints.
After $k-2$ of such steps we obtain the depth 2 and the number of free variables
$$m := n\cdot \sigma^{k-2} = \frac{n}{(20w)^{k-2}} = \frac{n}{(400\log_2 S)^{k-2}}.$$

By Lemma 11.3, the constraint $\mathrm{PARITY}_n\upharpoonright\rho$ is $\mathrm{PARITY}_m$ or its negation.

5) But by Theorem 10.3 any depth-2 DNF/CNF for $\mathrm{PARITY}_m$
requires size $\ge 2^{m-1}$. The size of our formula after restrictions
does not exceed $S$, which means $S\ge 2^{m-1}$ and, therefore, $m=O(\log_2 S)$.

Substituting $m=\Theta\big(n/(\log_2 S)^{k-2}\big)$, we get
$(\log_2 S)^{k-1}=\Omega(n)$, that is, $\log_2 S=\Omega(n^{1/(k-1)})$.
Therefore, $S\ge 2^{\Omega(n^{1/(k-1)})}$. $\square$

**Goal for continuation:** or write out the proof of Theorem 11.1
(switching lemma), or fix one selected link as "trusted"
and then move on to other models/functions.
