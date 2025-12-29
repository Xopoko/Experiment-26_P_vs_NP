## 15. Proof complexity: resolution and PHP

In proof complexity, **lengths of proofs** are studied.
Strong lower bounds are possible in weak systems, but transfer to strong ones
associated with $\mathrm{NP}$ vs $\mathrm{coNP}$.

**Definition (proof system, Cook-Reckhow; roughly).** For the $L\subseteq\Sigma^\*$ language this is a polynomial verifier $V(x,\pi)$, where:
- *(sound)* $V(x,\pi)=1 \Rightarrow x\in L$;
- *(completeness)* $x\in L \Rightarrow \exists \pi,\ |\pi|\le \mathrm{poly}(|x|):\ V(x,\pi)=1$.

**Lemma 15.1 (Cook-Reckhow, 1979).** $\mathrm{NP}=\mathrm{coNP}$ then
and only if there is a polynomially bounded proof system
for $\mathrm{TAUT}$.

*Proof.* If $\mathrm{TAUT}$ has a pbounded proof system,
then $\mathrm{TAUT}\in\mathrm{NP}$ and $\mathrm{coNP}\subseteq\mathrm{NP}$,
means $\mathrm{NP}=\mathrm{coNP}$.
Conversely, if $\mathrm{NP}=\mathrm{coNP}$, then $\mathrm{TAUT}\in\mathrm{NP}$ is a pbounded proof system. $\square$

**Corollary (reformulation).** Existence of a pbounded proof system
for $\mathrm{TAUT}$ $\Rightarrow$ $\mathrm{NP}=\mathrm{coNP}$ (by Lemma 15.1).

**Resolution.** We work with CNF. Rule: from $(A\lor x)$
and $(B\lor\neg x)$ we output $(A\lor B)$.
*Refutation* $F$ - derivation of an empty clause from clauses $F$.

**CNF formulation of the Dirichlet principle (PHP):** Let the variable $x_{i,j}$
means "pigeon $i$ is sitting in hole $j$." CNF $\mathrm{PHP}^{n}_{m}$ consists of:
- *(the bird is sitting somewhere)* $\forall i$: $x_{i,1}\lor\cdots\lor x_{i,n}$;
- *(not together)* $\forall j,\ i\ne i'$: $(\neg x_{i,j}\lor\neg x_{i',j})$; for $m=n+1$ the formula is impossible.

**Theorem 15.2 (Haken, 1985).** There is a constant $c>1$ such that any
resolution refutation $\mathrm{PHP}^{n}_{n+1}$ has size $\ge c^n$
(that is, $2^{\Omega(n)}$).

*Comment.* Complete proof using the "critical assignments -> positive version -> constraints" (TSS) scheme.
See `../resources/downloads/tss_proof_complexity_notes.pdf`, Thm 2 (Hak85), Sec. 3.

Modern "packaging" of such results: the connection between size and *width*
(Ben-Sasson-Wigderson, 2001). It is especially useful for 3CNF
(where the initial width is constant).

**Definition (resolution width).** Output width is the maximum number of literals in a clause found in the resolution output.

**Theorem 15.3 (BenSasson-Wigderson, 2001).** Let $F$ be a CNF on $N$ variables,
$w_0$ is the maximum width of the original clauses, $W$ is the minimum width
resolution refutation.
Then the size of any refutation is $\ge 2^{\Omega((W-w_0)^2/N)}$.

**Note.** Size-width requires small $w_0$ and control of the number of variables; see Ben-Sasson-Wigderson, Sec. 4, and TSS/de Wolf.

### 15.4. Critical assignments and the "positive version" (complete proof)

Next, it is useful to fix a subset of assignments in which negations can be replaced by "positive" disjunctions.

**Definition (critical assignment).** For $\mathrm{PHP}^{n}_{n+1}$
assignment $\alpha$ *critical* if index exists
$i_0\in\{1,\dots,n+1\}$ such that:
- for each $j\in\{1,\dots,n\}$ there is **exactly one** $i\ne i_0$ with $x_{i,j}(\alpha)=1$ (each hole is occupied by exactly one pigeon);
- for each $i\ne i_0$ there is **exactly one** $j$ with $x_{i,j}(\alpha)=1$ (each of the other pigeons sits in exactly one hole);
- for $i=i_0$, $x_{i_0,j}(\alpha)=0$ is true for all $j$ (one "extra" pigeon does not sit anywhere).

**Definition (positive replacement of negation).** Define
$$X_{i,j}:=\bigvee_{i'\ne i} x_{i',j}.$$
For a clause $C$ over $x_{i,j},\neg x_{i,j}$ we define $C^+$ as a replacement
each $\neg x_{i,j}$ on $X_{i,j}$ with opening; $C^+$ is a positive clause.

**Lemma 15.4.** For any critical $\alpha$ and any clause $C$, $C(\alpha)=C^+(\alpha)$ is true.

*Proof.* At critical $\alpha$, each column of $j$ contains exactly one unit. Therefore, for any $i,j$:

- if $x_{i,j}(\alpha)=1$, then all $x_{i',j}(\alpha)=0$ for $i'\ne i$, which means $X_{i,j}(\alpha)=0$ and also $(\neg x_{i,j})(\alpha)=0$;
- if $x_{i,j}(\alpha)=0$, then the unit in the column $j$ is
  in some line $i'\ne i$, then $X_{i,j}(\alpha)=1$
  and also $(\neg x_{i,j})(\alpha)=1$.

So, on critical assignments $\neg x_{i,j}$ is equivalent to $X_{i,j}$,
which means that any clause retains its meaning with such a replacement. $\square$

(The code for checking Lemma 15.4 for small $n$ is in the next cell.)

### 15.5. "Broad clause" in the positive version (full proof)

Let's fix $\mathrm{PHP}^{n}_{n+1}$ and critical assignments from section 15.4.

**Definition.** $\mathrm{Pigeon}(C)$ are the indices $i$ for which there is
$i$-critical $\alpha$ with $C(\alpha)=0$; $\mu(C):=|\mathrm{Pigeon}(C)|$.

**Lemma 15.5 (wide clause).** For any resolution refutation $\mathrm{PHP}^{n}_{n+1}$ there is a clause $C$ from the derivation such that
$$\mathrm{width}(C^+)\ \ge\ \frac{2(n+1)^2}{9}\ =\ \Omega(n^2).$$

*Proof.*

1) For each $i$, the clause $P_i:=(x_{i,1}\lor\cdots\lor x_{i,n})$ has $\mu(P_i)=1$: it is false exactly at $i$-critical ones.

2) For an empty clause $\emptyset$ we have $\mu(\emptyset)=n+1$, since $\emptyset(\alpha)=0$ on any assignment.

3) If $C$ is the resolvent of $A,B$, then $\mu(C)\le\mu(A)+\mu(B)$:
at critical $\alpha$ with $C(\alpha)=0$ $A$ or $B$ is false,
this means the index is taken into account in $\mathrm{Pigeon}(A)$ or $\mathrm{Pigeon}(B)$.

Let's take the first clause $C$ in the derivation with $\mu(C)>(n+1)/3$.
It exists since $\mu(P_i)=1$ and $\mu(\emptyset)=n+1$.
By (3) such a $C$ satisfies $\mu(C)\le 2(n+1)/3$.

Let us set $s:=\mu(C)$, so that $(n+1)/3 < s\le 2(n+1)/3$.

Now we will show that $\mathrm{width}(C^+)\ge s((n+1)-s)$. Let us take $i\in\mathrm{Pigeon}(C)$ and $i$-critical $\alpha$ with $C(\alpha)=0$.
For any $j\notin\mathrm{Pigeon}(C)$ we construct a $j$-critical $\alpha'$ by permuting the strings $i$ and $j$ (the pigeon $i$ lands in the hole $j$).

Since $j\notin\mathrm{Pigeon}(C)$, we have $C(\alpha')=1$. By Lemma 15.4 we obtain $C^+(\alpha)=0$ and $C^+(\alpha')=1$.

The clause $C^+$ is positive. The transition $\alpha\to\alpha'$ changes the only $x_{i,k}$ (hole $j$), which means $x_{i,k}$ is included in $C^+$.

For a fixed $i$, different $j$ give different $k$, which means that from the string $i$ we get $\ge(n+1)-s$ literals in $C^+$.
Summing over all $i\in\mathrm{Pigeon}(C)$, we have $\mathrm{width}(C^+)\ge s((n+1)-s)$.

Since the function $s((n+1)-s)$ on the interval $(n+1)/3 < s\le 2(n+1)/3$ is minimal at the ends, we have $s((n+1)-s)\ge 2(n+1)^2/9$. $\square$

### 15.6. Constraints on $\Rightarrow$ exponent (full proof)

Let $R$ be the resolution refutation of $\mathrm{PHP}^{n}_{n+1}$.
Let's put $m:=n+1$ (number of pigeons) and $N:=n(n+1)=m(m-1)$
(number of variables $x_{i,j}$).

Let us fix $\varepsilon\in(0,1)$ and call the clause $C\in R$
*$\varepsilon$wide* if $\mathrm{width}(C^+)\ge \varepsilon N$.
Let $S$ be the number of such clauses.

**Lemma 15.6.1.** There is a variable $x_{i,j}$, which is included
at least in $\varepsilon S$ $\varepsilon$broad clauses
(in their positive versions).

*Proof.* Every $\varepsilon$broad clause contains
$\ge \varepsilon N$ literals, meaning a total of $\ge \varepsilon N\cdot S$ occurrences.
According to Dirichlet, there is a variable included in at least
$(\varepsilon N\cdot S)/N=\varepsilon S$ of such clauses. $\square$
According to Dirichlet, there is a variable included in at least $(\varepsilon N\cdot S)/N=\varepsilon S$ of such clauses. $\square$

Let us choose such a variable $x_{i,j}$ and consider the constraint $\rho$,
which "puts" pigeon $i$ into hole $j$:
$$x_{i,j}=1,\quad x_{i',j}=0\ (i'\ne i),\quad x_{i,j'}=0\ (j'\ne j).$$
After this limitation, the original CNF naturally turns
in $\mathrm{PHP}^{n-1}_{n}$ (remove row $i$ and column $j$).

**Lemma 15.6.2.** If we apply $\rho$ to all clauses of the derivation of $R$
(removing true clauses and false literals), we get a refutation
$\mathrm{PHP}^{n-1}_{n}$.

*Proof.* A constraint is a substitution and a simplification.
The resolution is closed: if $C$ is the resolvent of $A,B$, then
$C\upharpoonright\rho$ is the resolvent of $A\upharpoonright\rho,B\upharpoonright\rho$
or should be trivial.
An empty clause is preserved, which means the image is a correct conclusion. $\square$

**Lemma 15.6.3.** After applying $\rho$, the number of $\varepsilon$-wide clauses in $R$ decreases by at least $(1-\varepsilon)$ times.

*Proof.* All $\varepsilon S$ wide clauses with $x_{i,j}$
become true and disappear. The rest just lose literals,
new $\varepsilon$wide ones do not appear. $\square$

After one step: refutation $\mathrm{PHP}^{n-1}_{n}$, number of wide clauses
$\le (1-\varepsilon)S$.
After $k$ steps: refutation $\mathrm{PHP}^{n-k}_{n+1-k}$,
number of wide clauses $\le S(1-\varepsilon)^k$.

Let's choose $k:=\left\lceil\frac{\ln S}{\varepsilon}\right\rceil+1$.
Since $1-\varepsilon\le e^{-\varepsilon}$,
$$S(1-\varepsilon)^k\le S e^{-\varepsilon k}<1.$$ 
This means that after $k$ steps there are no $\varepsilon$wide clauses: for any $D$
we get $\mathrm{width}(D^+)<\varepsilon N\le \varepsilon m^2$.

On the other hand, apply Lemma 15.5 to $\mathrm{PHP}^{n-k}_{n+1-k}$: there is a clause $D$ such that
$$\mathrm{width}(D^+)\ge \frac{2(n+1-k)^2}{9} = \frac{2(m-k)^2}{9}.$$ 
So definitely
$$\frac{2(m-k)^2}{9}<\varepsilon m^2,$$
that is, $m-k<\frac{3}{\sqrt2}\sqrt\varepsilon\,m$ and
$$k>\Bigl(1-\tfrac{3}{\sqrt2}\sqrt\varepsilon\Bigr)m.$$ 

But by definition $k\le \frac{\ln S}{\varepsilon}+2$, therefore
$$\ln S\ \ge\ \varepsilon\Bigl(1-\tfrac{3}{\sqrt2}\sqrt\varepsilon\Bigr)m\ -\ 2\varepsilon.$$
We take $\varepsilon=1/100$, then $\ln S=\Omega(m)=\Omega(n)$,
that is, $S\ge 2^{\Omega(n)}$. Since $S\le |R|$, this is an exponential
lower estimate. Theorem 15.2 is proven. $\square$

### 15.7. Beyond Resolution: What is Known and What is Open

Resolution is a weak system. These lower bounds do not approximate $\mathrm{NP}$ vs $\mathrm{coNP}$.
We need estimates for **significantly stronger** proof systems (Cook-Reckhow).

**Definition (p-bounded).** Proof system $P$ -- p-bounded if for any
tautology $\varphi$ there is a $P$-proof of size
$\mathrm{poly}(|\varphi|)$.

**Definition (p-simulation).** $P$ p-simulates $Q$ if the polynomial
function transforms $Q$-proof $\pi$ into $P$-proof of the same
tautologies.
Size is $\mathrm{poly}(|\pi|)$.

**Definition (p-optimal system).** $P$ is p-optimal if
p-simulates all systems. The question of existence is open.

Map of systems and overview of lower estimates: Urquhart 1996
(`../resources/downloads/urquhart_1996_complexity_of_propositional_proofs.pdf`).

**Corollary (guideline).** If a p-optimal system exists for it
superpolynomial lower bounds have been proven, then $\mathrm{NP}\ne\mathrm{coNP}$
(and therefore $\mathrm{P}\ne\mathrm{NP}$).

**Contrast using PHP as an example.**
- *(Frege easy)* Polynomial proofs $\mathrm{PHP}$: Buss (1987), `../resources/downloads/buss_1987_php_frege.pdf`.
- *(boundeddepth Frege hard)* Exponential lower bounds for $\mathrm{PHP}$:
  Beame et al. (1992), `../resources/downloads/beame_et_al_1992_php_bounded_depth_frege.pdf`.
- *(Cutting Planes easy)* Polynomial refutations $\neg\mathrm{PHP}$:
  Buss–Clote (2002), `../resources/downloads/buss_cutting_planes_notes.pdf`.

**Open goal of the proof complexity line.** Superpolynomial lower bounds for strong systems on explicit tautologies.
If for p-optimal (if any) or for all, then $\mathrm{NP}\ne\mathrm{coNP}$
(and $\mathrm{P}\ne\mathrm{NP}$), but EF alone is not enough.
Conditional connective: Pich-Santhanam (2023) gives $\mathrm{P}\ne\mathrm{NP}$
from EF-lower bounds under the assumptions: $\mathrm{S}^1_2$-formalizable reductions
and medium difficulty.
Thm 1, 7–9: `../resources/downloads/pich_santhanam_2023_ef_lower_bounds.pdf`.

**Definition (Pich-Santhanam, introduction).** For $k\ge 1$ and ptime function $f$
enter a template formula
$$w_{n,k}(f) := [\mathrm{SAT}_n(x,y)\to \mathrm{SAT}_n(x,C(x))]\ \lor
[\mathrm{SAT}_n(f_1(C),f_2(C))\wedge \neg\mathrm{SAT}_n(f_1(C),C(f_1(C)))].$$
Here $C$ is the circuit code of size $n^k$; $\mathrm{SAT}_n(x,y)$: $y$ satisfies
formula $x$ of size $n$; $f(C)=\langle f_1(C),f_2(C)\rangle$.
Intuition: $w_{n,k}(f)$ is a tautology $\iff$ $f$ **indicates an error**
any circuit $C$ that does not solve searchSAT on length $n$.
**Definition (Pich-Santhanam, introduction/Sec. 2.2).** $W_{n,k}(f)$:
"natural" $\forall\Pi^b_1$-formulation $\exists n_0\,\forall n>n_0$
formulas $w_{n,k}(f)$ are tautologies.

**Definition (S$^1_2$).** $\mathrm{S}^1_2$ - Buss theory of limited
arithmetic in $L_{BA}$; bounded quantifiers and $\Sigma^b_1$induction on $|x|$.
Used to formalize ptime reasoning (Buss 1995; Krajicek 1995; Cook-Nguyen 2010).

**Reminder (restricted quantifiers).** In $L_{BA}$: $\forall x\le t$, $\exists x\le t$
(abbreviations $\forall x(x\le t\to\varphi)$, $\exists x(x\le t\wedge\varphi)$).
$|x|$ is the length of the binary record.
(Buss 1995; Krajíček 1995; Cook–Nguyen 2010).

**Reminder ($\Sigma^b_1$formulas).** Leading block of limited existences
(e.g. $\exists y\le t(x)\,\psi$), matrix $\psi$ is bounded ($\Delta^b_0$).
(Buss 1995; Krajíček 1995; Cook–Nguyen 2010).

**Lemma-bridge (S$^1_2$ -> EF; quoted).** If $\Pi^b_1$formula $\varphi$
is provable in $\mathrm{S}^1_2$, then the translations of $\lVert\varphi\rVert_n$ have
polynomial EF proofs.
(Pich–Santhanam, Sec. 2.2; Buss 1995; Krajíček 1995; Cook–Nguyen 2010.)

**Theorem (Pich-Santhanam, Theorem 1; cited).** There is a universal constant $\varepsilon>0$ such that for any $k\ge 1$:
- if $w_{n,k}(f)$ are tautologies for all large $n$ and the system
  $\mathrm{EF}+w_k(f)$ is not polynomially bounded, then
  $\mathrm{SAT}\notin\mathrm{SIZE}(n^{\varepsilon k})$ infinitely often;
- if $\mathrm{S}^1_2\vdash W_{n,k}(f)$ and EF is not polynomial bounded, then the same conclusion.

**Landmark (Pich-Santhanam, Abstract).** Subject to two prerequisites
on provability in $\mathrm{S}^1_2$ (hardness in $\mathrm{E}$
and "learning from $\neg\exists$OWF")
and given an explicit family of functions for which EF *doesn't* have polynomial
proofs of correct lower bound schemes follows $\mathrm{P}\ne\mathrm{NP}$.
In the wording of the annotation (briefly):
Let further $t(n):=1/2-1/2^{n/4}$.
1) (I) $\mathrm{S}^1_2$ proves for explicit $h_0\in\mathrm{E}$:
   $tt(h_{0,n},2^{n/4},t(n))$ -- tautologies for large $n$
   (hardness of approximation; Thm 8/9).
   *(Formalization $h_0\in\mathrm{E}$):* $h_0$ is computable in $2^{O(n)}$ (bounded-check machine in $\mathrm{S}^1_2$).
2) (II) $\mathrm{S}^1_2\vdash \forall n\,\forall C\,\exists y\le\mathrm{poly}(n)$
   $\mathrm{RedCorr}(n,C,y)$ for the reduction "$\neg\exists$OWF -> learning" (Thm 9).
   $\mathrm{RedCorr}(n,C,y)$: "$y$ is a correct output to $(n,C)$ and error $< t(n)$" (bounded formulation).
3) (IIa) "$\neg\exists$OWF": for any p-time $f$ there is a p-time inverter
   $A$ and a polynomial $p$ with $\Pr[A(f(x))=x]\ge 1/p(n)$ infinitely often.
It is encoded in $\mathrm{S}^1_2$ through bounded quantifiers (Cook-Nguyen 2010, ch. 11).

The checklist is in the "Open Steps" below.
See also (alternative thread): algebraic proof systems (IPS)
and the connection with PIT/VP vs VNP (Grochow-Pitassi 2014;
`../resources/downloads/grochow_pitassi_2014_pit.pdf`).
VP/VNP+IPS Brief Map: Section 8, Point 4 (IPS is algebraic and not equivalent to EF).
Superpolynomial lower bounds IPS  VP=VNP; review/techniques:
Forbes–Shpilka–Tzameret–Wigderson 2021
(`../resources/downloads/forbes_shpilka_tzameret_wigderson_2021_ips.pdf`).

**Sanitary check (too strong canonization  collapse).** Let's fix the field $\mathbb F_p$.
For a literal we put $\llbracket x_i\rrbracket:=x_i$, $\llbracket\neg x_i\rrbracket:=1-x_i$.
For the clause $C=(\ell_1\lor\cdots\lor\ell_k)$ we put $S_C(x):=1-\prod_{t=1}^k(1-\llbracket\ell_t\rrbracket)$, and for CNF $\varphi=\bigwedge_j C_j$ - $P_\varphi(x):=\prod_j S_{C_j}(x)$.
Let $\mathrm{ML}(P)$ denote the reduction of $P\bmod(x_1^2-x_1,\dots,x_n^2-x_n)$ (the only multilinear polynomial coinciding with $P$ on $\{0,1\}^n$).
Then $\varphi$ is unsatisfiable $\iff \mathrm{ML}(P_\varphi)\equiv 0$ (on a cube $P_\varphi$ is an indicator, and for multilinear zero at $\{0,1\}^n$ means zero as a polynomial).
Therefore, if there is a ptime algorithm $\mathcal A$, which from $\varphi$ constructs a ROABP of polynomial size for $\mathrm{ML}(P_\varphi)$, then $\mathrm{UNSAT}\in\mathrm{P}$ through a deterministic PIT for ROABP, and hence $\mathrm{P}=\mathrm{NP}$.
PIT reference: Raz-Shpilka (2005), `../resources/downloads/raz_shpilka_2005_pit_noncommutative.pdf` (deterministic PIT for ABP in the noncommutative model; ROABP is a special case).

**Definition (IPS, rough).** IPS (Ideal Proof System) refutes the unsatisfiable CNF as an algebraic certificate.
After converting the clauses into polynomials $f_i$ over the field, a diagram is given,
calculating $g_i$ with $\sum_i g_i f_i = 1$; this is a refutation
(Grochow–Pitassi 2014).
The completeness of IPS follows from Nullstellensatz (`../resources/downloads/allcock_nullstellensatz_2005.pdf`).
Contrast: EF lower bounds  $\mathrm{NP}\ne\mathrm{coNP}$, IPS lower bounds  $\mathrm{VP}\ne\mathrm{VNP}$.
Status (IPS): General superpolynomial lower bounds remain open;
results are known only for limited subsystems
(refs: Grochow-Pitassi 2014; FSTW 2021, Sec. 1.3).

**Definition (PIT axioms; Grochow-Pitassi 2014, Def. 1.7).** We fix the standard coding of constant-free algebraic schemes. Let $K=\{K_{m,n}\}$ be a family of Boolean circuits that solve PIT for circuits of size $m$ over $n$ variables of polynomial degree. The PIT axioms for $K$ (for all codes $[C],[G]$) are:
1) $K([C(x)])\to K([C(p)])$ (the zero polynomial is equal to zero on all Boolean inputs).
2) $K([C(x)])\to \neg K([1-C(x)])$ (if $C\equiv 0$, then $1-C\not\equiv 0$).
3) $K([G(x)])\wedge K([C(x,0)])\to K([C(x,G(x))])$ (substitution of the zero polynomial).
4) $K([C(x)])\to K([C(\pi(x))])$ (permutation of variables).

**Lemma 15.7.3 (PIT axioms  EF p-simulates IPS).** If there is a family $K$ of polynomial size computing PIT for constant-free circuits of polynomial degree, and EF has polynomial proofs of the PIT axioms for $K$, then EF p-simulates (and is in fact p-equivalent to) VP-IPS (Grochow-Pitassi 2014, Thm. 4.1). Here, the class of PIT circuits includes IPS certificates (polynomial size and degree).

*Proof (sketch).* IPS refutation is given by the circuit $C(x,y)$ with identities
$C(x,0)\equiv 0$ and $C(x,f(x))\equiv 1$ (that is, $1-C(x,f(x))\equiv 0$). PIT axioms
give EF the ability to prove these identities and their consequences on the Boolean cube:
from $K([C(x,0)])$ by (1) we obtain $C(a,0)=0$ for any Boolean $a$, and from
$K([1-C(x,f(x))])$ by (1) we obtain $C(a,f(a))=1$. If $a$ satisfies all
clauses, then $f(a)=0$ and by (3) $C(a,f(a))=C(a,0)=0$, a contradiction. Formalizing
SoundnessIPS, EF receives p-simulation IPS. $\square$

**Lemma 15.7.3a (SoundnessIPS; Grochow-Pitassi 2014, Sec. 4.1).** Let $\varphi=\kappa_1\wedge\cdots\wedge\kappa_m$ be a 3-CNF over $p_1,\dots,p_n$ and $Q_i^\varphi(x)$ be clauses polynomials of degree $\le 3$ (and added equations $x_i^2-x_i=0$). IPS refutation is a circuit $C(x,y)$ with $C(x,0)\equiv 0$ and $C(x,Q^\varphi(x))\equiv 1$. Let's define
$$\mathrm{ProofIPS}([C],[\varphi])\ :=\ K([C(x,0)])\ \wedge\ K([1-C(x,Q^\varphi(x))]),$$
A
$$\mathrm{SoundnessIPS}_{m,n}([C],[\varphi],p)\ :=\ \mathrm{ProofIPS}([C],[\varphi])\ \to\ \neg\mathrm{Truthbool}([\varphi],p).$$
If EF has polynomial proofs of the PIT axioms for $K$, then EF has polynomial proofs of $\mathrm{SoundnessIPS}$ (Lemma 4.4).

*Proof (sketch).* From $\mathrm{Truthbool}([\varphi],p)$ we derive $K([Q_i^\varphi(p)])$ for all $i$ (the clause polynomial vanishes at the true clause). Next, using axioms (1), (3), (4), we transfer the substitutions $p$ and $Q_i^\varphi$ inside $C$, obtaining $K([C(p,Q^\varphi(p))])$, and from $K([C(x,0)])$ - $K([C(p,0)])$. Then $K([1-C(x,Q^\varphi(x))])$ by (1) gives $K([1-C(p,Q^\varphi(p))])$, and axiom (2) gives a contradiction. The circuit $C$ has polynomial size and degree (VP-IPS), and the substitution $Q_i^\varphi$ preserves the polynomial degree, so $K$ is applicable. $\square$

**Lemma 15.7.3b (constants and degree; Grochow-Pitassi 2014, Sec. 1.2.1).** The PIT axioms are formulated for constant-free algebraic schemes. It's not important:
in a fixed finite field $\mathbb F_q$ constant-free is equivalent to the general case (there are a finite number of constants); over $\mathbb Z$ or $\overline{\mathbb F_p}$, polynomial bit-size constants are constructed by a constant-free circuit through binary expansion. Therefore, VP with polynomial total bit-size constants coincides with the constant-free option. IPS uses VP-IPS: polynomial size and polynomial degree. For 3-CNF, the polynomials $Q_i^\varphi$ have degree $\le 3$, and substituting $Q^\varphi$ into $C$ preserves the polynomial degree, which means the PIT scheme $K$ should work on schemes of polynomial degree.

**Lemma 15.7.3c (3-CNF without loss of generality).** Standard reduction transforms CNF into equisatisfactional 3-CNF with linear growth: clauses of length $\le 3$ are retained, and a clause of length $k>3$ is replaced by a chain of 3-clauses with new variables $(\ell_1\lor\ell_2\lor y_1)\wedge(\neg y_1\lor\ell_3\lor y_2)\wedge\cdots\wedge(\neg y_{k-3}\lor\ell_{k-1}\lor\ell_k)$. For a clause of length $k>3$ we obtain $k-2$ new clauses and $k-3$ new variables; if $\varphi$ has $L$ literals, then $r(\varphi)$ has $\le L$ clauses and $\le 3L$ literals (see Section 16.78). Then $\varphi$ is satisfiable, $\iff r(\varphi)$ is satisfiable, and EF proves $\neg r(\varphi)\to \neg\varphi$ through an explicit choice of new variables (see Lemma 15.7.3d). Therefore, SoundnessIPS formulated for 3-CNF is strong enough for the general case: one can first replace $\varphi$ with $r(\varphi)$ in the definition of $\mathrm{ProofIPS}$.

**Lemma 15.7.3d (equisatisfiable is sufficient; explicit choice of $g$).** In the CNF->3-CNF reduction, the formulas $\varphi$ and $r(\varphi)$ are only equisatisfiable (not logically equivalent in the same variables), but for SoundnessIPS equisatisfaction is sufficient: the undecidability of $r(\varphi)$ implies the undecidability $\varphi$. Moreover, there is an explicit polynomial function $g$ (over the values of the original variables) specifying the values of the new $y_i$ so that EF proves
$$\mathrm{Truthbool}([\varphi],p)\ \to\ \mathrm{Truthbool}([r(\varphi)],p,g(p)).$$
For the chain obtained from $(\ell_1\lor\cdots\lor\ell_k)$, we can take
$$y_i\ :=\ \neg(\ell_1\lor\cdots\lor\ell_{i+1})\quad (i=1,\dots,k-3),$$
which satisfies all new clauses for any true meaning of the original clause. From here
$$\neg\mathrm{Truthbool}([r(\varphi)],p,g(p))\to\neg\mathrm{Truthbool}([\varphi],p),$$
and therefore in SoundnessIPS there is enough equisatisfiable reduction.

**Barrier check (for 15.7.3-15.7.3d).**
- Relativization: the step is based on the correctness of the deterministic PIT; but there are oracles with $\mathrm{BPP}^A\ne\mathrm{P}^A$, so such a conclusion cannot be purely relativizing.
- Natural proofs: the output of PIT via circuit lower bounds is expected to fall under the Razborov-Rudich barrier in the presence of PRF.
- Algebrization: standard hard\-vs\-randomness de-randomization PIT is considered non-algebraizing; no algebraic proofs are known.

**Lemma 15.7.4 (weak ROABP barrier for CNF class).** Let $P_\varphi$ be the polynomial from the sanity check above, calculated by the depth-3 size formula $\mathrm{poly}(|\varphi|)$ (the product of clause polynomials $S_C$). If there is a p-time algorithm $\mathcal A$, which, using CNF $\varphi$, constructs a ROABP of size $\mathrm{poly}(|\varphi|)$ for $\mathrm{ML}(P_\varphi)$, then $\mathrm{UNSAT}\in\mathrm{P}$, and therefore $\mathrm{P}=\mathrm{NP}$.

*Proof.* Compute $R:=\mathcal A(\varphi)$ and apply deterministic PIT to ROABP. By the sanity check $\varphi$ $\iff \mathrm{ML}(P_\varphi)\equiv 0$ is unsatisfiable, so PIT solves UNSAT in polynomial time. $\square$

**Note:** The class $P_\varphi$ is the standard algebraic CNF (clause polynomials) encoding used in IPS/EF; the barrier already operates at such a minimal input.

**Lemma 15.7.4a (3-CNF sufficiency).** If there is a p-time algorithm $\mathcal A$ that, for any 3-CNF $\varphi$, constructs a ROABP of size $\mathrm{poly}(|\varphi|)$ for $\mathrm{ML}(P_\varphi)$, then $\mathrm{3\text{-}UNSAT}\in\mathrm{P}$, therefore $\mathrm{P}=\mathrm{NP}$.

*Proof.* For 3-CNF $\varphi$, calculate $R:=\mathcal A(\varphi)$ and apply deterministic PIT to ROABP. According to the sanity check $\varphi$ $\iff \mathrm{ML}(P_\varphi)\equiv 0$ is not feasible, which means $\mathrm{3\text{-}UNSAT}\in\mathrm{P}$. Since $\mathrm{3\text{-}UNSAT}$ is coNP-complete and $\mathrm{P}$ is complement closed, we obtain $\mathrm{P}=\mathrm{NP}$. $\square$

**Lemma 15.7.4b (NP-complete subclasses of CNF).** Let $\mathcal C$ be a subclass of CNF for which there exists a p-time reduction of $r$ from 3-CNF to $\mathcal C$ that preserves (un)satisfiability and satisfies $|r(\varphi)|\le\mathrm{poly}(|\varphi|)$. If there is a p-time algorithm $\mathcal A$, which, using $\psi\in\mathcal C$, constructs a ROABP of size $\mathrm{poly}(|\psi|)$ for $\mathrm{ML}(P_\psi)$, then $\mathrm{P}=\mathrm{NP}$.

*Proof.* For an arbitrary 3-CNF $\varphi$, construct $\psi=r(\varphi)$ and apply $\mathcal A$ to $\psi$, then PIT for ROABP. By the sanity check $\psi$ $\iff \mathrm{ML}(P_\psi)\equiv 0$ is unsatisfiable, and by the correctness of $r$ this is equivalent to the unsatisfiability of $\varphi$. This means $\mathrm{3\text{-}UNSAT}\in\mathrm{P}$, that is, $\mathrm{P}=\mathrm{NP}$. Polynomial growth of $|r(\varphi)|$ does not change the requirement $\mathrm{poly}(|\psi|)=\mathrm{poly}(|\varphi|)$. $\square$

**Lemma 15.7.4c (accounting for blow-ups).** Let the reduction $r$ satisfy $|r(\varphi)|\le |\varphi|^c$ and the algorithm $\mathcal A$ constructs a ROABP of size $\le |\psi|^d$ for input $\psi$. Then the composition gives a ROABP of size $\le |\varphi|^{cd}$ for the original 3-CNF. Therefore, any polynomial blow-up reduction only changes the constant to a power and does not affect the derivation of $\mathrm{P}=\mathrm{NP}$ in Lemma 15.7.4b.

**Lemma 15.7.4d (concrete NP-complete subclasses).** Planar 3-SAT NP-complete (Lichtenstein 1982, `../resources/downloads/lichtenstein_1982_planar_formulae.pdf`); in its reduction the size grows no more than quadratically: $|r(\varphi)|=O(|\varphi|^2)$ (see Section 16.83). Moreover, Planar3SAT(<=4occ) is NPcomplete (Lichtenstein composition and Section 16.84). Moreover, 3-SAT with the constraint "each variable appears at most 4 times" is NP-complete: NP-hardness follows from the explicit linear reduction 3-SAT -> 3-SAT(<=4-occ) in Section 16.81-16.82, and membership of NP is trivial. Therefore, for these subclasses of $\mathcal C$ the premise of Lemma 15.7.4b (p-time reduction from 3-CNF with polynomial blow-up) is satisfied.

**Counterexample (monotone CNFs).** The restriction on monotone clauses is too strong: any monotone CNF without an empty clause is satisfied (assigning all variables to 1), so even perfect canonization on this class does not give NP-hardness.

**Barrier check (for 15.7.4-15.7.4d).**
- Relativization: if $\mathcal A$ is relativized, then for any oracle $A$ we obtain $\mathrm{P}^A=\mathrm{NP}^A$, which contradicts BGS.
- Natural proofs: the construction of such $\mathcal A$ through constructive/large-scale properties falls under the Razborov-Rudich barrier in the presence of PRF.
- Algebrization: the collapse of $\mathrm{P}=\mathrm{NP}$ is not algebraizing, which means that the proof of the existence of $\mathcal A$ cannot be purely algebraizing.

**Skeleton of the proof (for step 2).** See also the L2/RedCorr skeleton above.
Parameters: fix the constants $a,t$ (from Theorem 9), consider $n$ sufficiently large.
Formalization in $\mathrm{S}^1_2$: definitions $\mathrm{Enc}$, $\mathrm{Len}$
and the reductions $R$ must be bounded (lemma-bridge EF$\leftrightarrow\mathrm{S}^1_2$).
Hint: The formula for $\mathrm{Enc}$ quantifies the string indices $i\le |\pi|$ and checks local inference rules and axioms.
Similarly, $\mathrm{Len}$ is specified through the code length predicate, and the reduction $R$
is given by the p-time computable function (Sec. 2.2 in Pich-Santhanam).
Result: L2/L3 remain open; they are the ones that require a non-trivial EF-lower bound.
Candidates: PHP, Tseitin (XOR parities on edges), Clique-Coloring.
References: Beame-Sabharwal 2000, `../resources/downloads/beame_sabharwal_2000_proof_complexity.pdf`.
Buss 1997, `../resources/downloads/buss_1997_proof_complexity_intro.pdf`.
Hrubeš 2013, `../resources/downloads/hrubes_2013_interpolation_technique.pdf`.
Feasible interpolation: short proofs clique-coloring  small
monotonous patterns (Tabatabai 2025, `../resources/downloads/tabatabai_2025_feasible_interpolation.pdf`).
Monotonic lower bounds for CLIQUE: Razborov 1985, `../resources/downloads/razborov_1985_monotone.pdf`.
Scheme: small proofs + (monotonic) interpolation  small monotonic schemes;
contraposition + Razborov  lower estimates for evidence.
Other candidates: random $k$CNF; CNF "NP has no small circuits" (Razborov 2023).
For Tseitin on expanders, exponential lower bounds on resolution in terms of width/expansion are known; Itsykson-Oparin 2013.
Formally: for $\deg(G)\le k$ we have $W\ge e(G)-1$ and $S\ge 2^{(e(G)-k-1)^2/|E|}$, which means on boundeddegree expanders $S=2^{\Omega(|V|)}$; see Section 16.85-16.86.
With an explicit expander family, this gives an explicit bounded-occ family 3-CNF (see Section 16.87).
For Tseitin(Grid$_{n,n}$) (where the number of variables $N=\Theta(n^2)$) in boundeddepth Frege only spaced boundaries for polynomialsize are known:
depth $=\Omega(\log_2 N/\log_2\log_2 N)$ (Hastad'20, Cor. 6.6) and depth $=O(\log_2 N)$ (upper from GIRS'19; see Section 16.92+Section 16.115+Section 16.116+Section 16.120).
**Q39 (frontier as undirected slice).**
IN `formal/WIP/Verified/Q39.lean` introduced `frontier` as a union of oriented boundaries.
Invariance has been proven for symmetric graphs `frontier` when replacing $S$ with $\\neg S$.
This allows frontiers to be viewed in two-lane increments without orientational ambiguity.
Lemma: `Q39_frontier_compl` (see `formal/WIP/Verified/Q39.lean`).
**Q39 (frontier → adjacency).**
For symmetric graphs it has been proven that any `frontier`- the edge is really
is an edge of the graph (in the undirected sense).
This removes the technical difference between orientation in `boundary` and the edge of the cut
when moving to rank/interval estimates.
Lemma: `Q39_frontier_adj` (see `formal/WIP/Verified/Q39.lean`).
**Q39 (two‑strip toy rank).**
Toy for $n=4$: even if each internal node has
$|S_j\\cap\\delta(U)|\\le 2$ and $|S_{j+1}\\cap\\delta(U)|\\le 2$, projection rank on two blocks
remains equal to 2 (the upper/lower halves of the stripes give independent projections).
See `formal/Notes/TseitinQ39.lean` §16.167 (Q39.S23-2k-two-strip-rank-toy).
**Q39 (balanced anchored blocks).**
Toy at $k=2$: even with "balanced" anchor blocks in a fixed schedule
two different non-zero projections remain distinguishable, so the rank does not fall below 2.
IN `formal/WIP/Verified/Q39.lean` two balanced 12bit projections are recorded
and lemma `Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced`.
This closes the attempt to "balance" the anchored steps in the two-way model.
**Q39 (row/column swap symmetry).**
Toy at $k=2$: even with symmetry between stripes (row/column swap)
the two strip-symmetric nonzero projections remain distinguishable, so rank 2 is preserved.
IN `formal/WIP/Verified/Q39.lean` two such projections and the lemma are fixed
`Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap`.
This rules out simple strip symmetrization as a rank reduction mechanism.
**Q39 (fixed‑pair row/column swap).**
Toy for $k=2$: even with a fixed row/column pair and mandatory row/column swap
the two non-zero projections remain distinguishable, so rank 2 is preserved.
IN `formal/WIP/Verified/Q39.lean` such projections and lemma are fixed
`Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair`.
This rules out "fixed-pair swap" as an easy path to rank 1.
**Q39 (fixed‑pair + same‑order).**
Toy for $k=2$: even with a fixedpair and the same order in both stripes
the two non-zero projections remain distinguishable, so rank 2 is preserved.
IN `formal/WIP/Verified/Q39.lean` such projections and lemma are fixed
`Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder`.
This rules out same-order as a simple rank reduction mechanism in fixed-pair mode.
**Q39 (global fixed‑pair).**
Toy for $k=2$: even with a fixed pair on the entire chain
the two non-zero projections remain distinguishable, so rank 2 is preserved.
IN `formal/WIP/Verified/Q39.lean` such projections and lemma are fixed
`Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair`.
This rules out global fixed-pair as an easy path to rank 1.
**Q39 (contiguous shift alt8).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt8`).
**Q39 (contiguous shift alt9).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt9`).
**Q39 (contiguous shift alt10).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt10`).
**Q39 (contiguous shift alt11).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt11`).
**Q39 (contiguous shift alt12).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt12`).
**Q39 (contiguous shift alt13).**
Toy with $k=2$: next cyclic shift of contiguous blocks with fixed orientation
still gives two different non-zero projections, so the rank remains 2.
See `formal/WIP/Verified/Q39.lean` (`Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt13`).
**Q43 (flat local-EF(s), parameter-summary).**
With explicit $A\le 668$ from HR'22 we obtain $n_0(A)=2$, therefore in HR mode
condition $n\ge n_0(A)$ is redundant compared to $n\ge 20 C n' \log_2 n'$
(for $C\ge 3$ and $t\le s\le n'/32$). The final summary leaves
the only $n$-barrier $n \ge 20 C n' \log_2 n'$ and other prerequisites unchanged.
See `formal/Notes/TseitinLocalEF.lean` §16.275 (Q43.S132-update-summary-dominant-bound).
**Q43 (compatibility after $t\mapsto(2s+1)t$).**
For $M=\mathrm{poly}(n)$ and $s=\mathrm{polylog}(n)$ we have $t'=(2s+1)\log_2 M=(\log_2 n)^{O(1)}$,
and HR recursion gives $n_\eta \ge n/\mathrm{polylog}(n)^\eta$ with $\eta\le d=O(\log_2 n/\log_2\log_2 n)$.
This ensures compatibility of the conditions $t'(d)\le n_d/16$ and $t'\le s_\eta\le n'/32$
for sufficiently large $n$; it is possible to replace $s_1=\log_2 N$ with $s_1=\max\{\log_2 N,t'\}$ without changing
asymptotics (see Section 16.276, Q43.S133-hr-compatibility-check).
**Q43 (axiom-size bound).**
If in flat local-EF(s) the size of the proof $S$ is measured by the size of the strings and
extension axioms $p_i\leftrightarrow\varphi_i(X)$ are included as strings, then $|\varphi_i|\le S$.
Then for any string $F$ the expansion size is $M(F)\le |F|+|F|\cdot\max_i|\varphi_i|\le S+S^2$,
therefore $t=\log_2 M(F)=O(\log_2 S)$, and for $S=\mathrm{poly}(n)$ we get $t=O(\log_2 n)$.
If the axioms are not taken into account in size, one can take $|\varphi_i|=2^{(\log_2 n)^2}$ for
$|\mathrm{supp}(\varphi_i)|\le s$, and then $t$ becomes superpolynomial.
See `formal/Notes/TseitinLocalEF.lean` §16.332 (Q43.S192-flat-eval-axiom-size-bound).
**Q43 (size metric formalized).**
IN `formal/WIP/Verified/Q43.lean` definitions of line-size/line-count/line-max are fixed
and lemma: if a string is included in proof, then its size does not exceed the total size of proof.
This provides a formal kernel for the $(N,M)$ metric and for controlling $M$ through the total size.
See `formal/WIP/Verified/Q43.lean` (Q43_lineSize/Q43_proofSize/Q43_lineSize_le_proofSize).
**Q43 (t parameter formalized).**
IN `formal/WIP/Verified/Q43.lean` the parameter $t:=\\log_2 M$ is introduced as `Nat.log2 M` and
the estimate $t\\le M$ is proved (lemma `Q43_tParam_le`). This fixes the basic
relationship between line-size $M$ and depth of evaluations in Q43.
See `formal/WIP/Verified/Q43.lean` (Q43_tParam/Q43_tParam_le).
**Q43 (t bounded by proof size).**
IN `formal/WIP/Verified/Q43.lean` it has been proven that `lineMax` does not exceed the total
proof size (`Q43_lineMax_le_proofSize`), which means
$t=\\log_2(\\mathrm{lineMax})\\le\\mathrm{proofSize}$ via `Q43_tParam_le_proofSize`.
This gives a formal connection between $t$ and the general size metric.
See `formal/WIP/Verified/Q43.lean` (Q43_lineMax_le_proofSize/Q43_tParam_le_proofSize).
**Q43 (t <= log_2 S).**
IN `formal/WIP/Verified/Q43.lean` the monotonicity of $\\log_2$ on Nat is proved and the lemma
$t=\\log_2(\\mathrm{lineMax})\\le\\log_2(\\mathrm{proofSize})$.
This formalizes the relationship $t \\le \\log_2 S$ with $S=\\mathrm{proofSize}$ (logarithm of base 2).
See `formal/WIP/Verified/Q43.lean` (Q43_log2_mono/Q43_tParam_le_log2_proofSize).
**Q43 (t = O(log_2 n) for poly-size).**
If the total size of $S(n)$ is polynomial, $S(n)\\le n^k+1$, then for $n\\ge 2$
we have $S\\le 2n^k$ and $t\\le\\log_2 S\\le 1+k\\log_2 n$, i.e. $t=O(\\log_2 n)$.
This relates Q43 estimates to the depth $O(\\log_2 n)$ mode at poly-size.
See `formal/Notes/TseitinLocalEF.lean` §16.340 (Q43.S200-flat-eval-tparam-ologn).
**Q43 (t = polylog n with quasi-poly size).**
If $S(n)\\le n^{(\\log_2 n)^c}=2^{(\\log_2 n)^{c+1}}$, then
$t\\le\\log_2 S\\le(\\log_2 n)^{c+1}$, i.e. $t=\\mathrm{polylog}(n)$ (base 2).
Note: for $c\\ge 1$ the function $2^{(\\log_2 n)^{c+1}}$ is superpolynomial.
See `formal/Notes/TseitinLocalEF.lean` §16.341 (Q43.S201-flat-eval-tparam-polylogn).
**Q43 (swap $s_1$).**
Replacing the starting $s_1=\log_2 N$ with $s_1=\max\{\log_2 N,t'\}$ does not break HR checks:
$s_\eta$ and $t(\eta)=\sum s_i+\log_2 M$ increase monotonically, and in the mode
$M=\mathrm{poly}(n)$, $s=\mathrm{polylog}(n)$ remains $t(\eta)\ll n_\eta$.
This removes the formal risk of inconsistency of the condition $t'\le s_\eta$ and preserves
$s_\eta\le n'/32$ for large $n$ (see Section 16.277, Q43.S134-s1-swap-compatibility).
**Q43 (audit $s_1$).**
In Proof of Thm. 4.3 HR'22 $s_1=\log_2 N$ appears only after
$s_\eta=2^{\eta-1}\log_2 N$ and $t(\eta)=\sum_{i\le\eta}s_i+\log_2 M$; in Lemma 4.5
only the sums $\sum s_i$ and the condition $t(\eta)\le n_\eta/16$ are used.
Direct occurrences of $\log_2 N$ in Proof of Thm. 4.3/Lemma 4.5 go only through
$s_\eta/t(\eta)$ and bound $t(d)\le 2^d\log_2 N+\log_2 M$, so the replacement $s_1$
influences only through $s_\eta/t(\eta)$ (see Section 16.278-Section 16.279, Q43.S135-S136).
The remaining $\log_2 N$ in Section 4 refers to Proof of Thm. 4.1 (singleswitching):
there $s=152\log_2 N$ is fixed and $t_d=152\log_2 N$ is used, but this is not included
in Proof of Thm. 4.3/Lemma 4.5 (see Section 16.280, Q43.S137-logn-remaining-scan).
**Q43 (explicit $A_0$ via $C$ from Lemma 5.5).**
IN `formal/WIP/Verified/Q43.lean` definition fixed `Q43_A0_from_C C := 78*C`.
This links "appropriate $A_0$" in Proof Lemma 4.2 to the constant $C$ from Lemma 5.5.
Lemma `Q43_A0_from_C_bound` reuses aggregation
$(A_0\\log n')\\,\\Delta^a\\,\\Delta^b=(A_0\\log n')\\,\\Delta^{a+b}$ for this choice $A_0$.
The next step is to make $C$ numeric (Chernoff constant), otherwise $A_0$ remains a parameter.
See `formal/WIP/Verified/Q43.lean`.
**Q43 (explicit $C$ and $A_0$ in Lean).**
IN `formal/WIP/Verified/Q43.lean` fixed Chernoff-constant `C=120000`
for the assessment from Section 16.308 when `exp=e^x` and `log=ln`.
From here `A0=78*C=9,360,000`, which is formalized as `Q43_A0_chernoff_ln`
and lemma `Q43_A0_chernoff_ln_eval`.
If `log=log2`, then $C$ is scaled by `ln 2`, therefore numerical
the meaning changes (the order is maintained).
See `formal/WIP/Verified/Q43.lean`.
**Q43 (pushing explicit $A_0$ into log factor).**
Lemma `Q43_A0_chernoff_ln_bound_explicit` rewrites the factor
$(A_0\\log n')\\,\\Delta^a\\,\\Delta^b$ in the form
$(9{,}360{,}000\\cdot\\log n')\\,\\Delta^{a+b}$.
This fixes the numerical value at the location where A0 comes into Proof Lemma 4.2.
and allows further convolution of the constants $c_1,c_2$ without hidden factors.
See `formal/WIP/Verified/Q43.lean`.
**Q43 (explicit $c_1,c_2$ in Thm. 4.1).**
From Section 16.302-Section 16.303 and Section 16.215 we take $A_{\\mathrm{bits}}=76$, which means $A=2^{76}$
(for binary counting; when moving to $\\ln$, replace with $e^{76\\ln 2}$).
We define $c_2:=8\\cdot 152\\cdot A$ and $c_1:=16\\cdot 152\\cdot c_2$ - by this
the phrases "large/some constant" in Proof Thm are eliminated. 4.1.
Recursion $n_i=\\lfloor n_{i-1}/(4A t\\log_2^4 n_{i-1})\\rfloor$ gives
$n_d\\ge n/(\\log_2^{d-1} N\\cdot(c_2\\log_2^4 n)^d)$ at $t=152\\log_2 N$.
The condition $\\log_2 N\\le n^{1/d}/(c_1\\log_2^4 n)$ provides $t_d\\le n_d/16$,
and Proof Thm. 4.1 completes the transition to Lemma 2.13; see Section 16.310 and
`formal/WIP/Verified/Q43.lean`.
**Q43 (explicit $c_1,c_2$ with numerical $A_0$).**
IN `formal/WIP/Verified/Q43.lean` values are fixed `c2` and `c1` when choosing
`A0=9,360,000` (from `C=120000` at `exp=e^x` and `log=ln`):
`c2=11,381,760,000` and `c1=27,680,440,320,000`.
This makes the formulas more specific `c2:=8*A0*152` and `c1:=16*152*c2` no hidden
multipliers; when moving to `log2` the numbers are scaled, but the scoring structure is the same.
See `formal/WIP/Verified/Q43.lean`.
**Q43 (log2 threshold Thm. 4.1 with explicit $c_1$).**
IN `formal/WIP/Verified/Q43.lean` predicate introduced
$\\log_2 n\\le n/(c_1\\log_2^4 n)$ with explicit numerical substitution
`c1=27,680,440,320,000`, and the multiplier is also fixed `c2` in the denominator.
This fixes log2 mode without hidden constants and prepares the check
bounds for the selected range $d$.
**Q43 (translation of $\\log_2 n$ to $|F|$ for grid).**
For grid-Tseitin we take $|F|=n^2$ and fix the definition `Q43_grid_size n := n^2`.
IN `formal/WIP/Verified/Q43.lean` it has been proven that for $n\\ge 1$ the following holds true:
$\\log_2 n\\le \\log_2 |F|$, so the log2 threshold can be expressed in terms of $|F|$.
Here exactly $\\log_2$ is used (without `exp`; the exhibitor base is not used).
See `formal/WIP/Verified/Q43.lean` (Q43_log2_le_log2_grid_size).
**Q43 (log2threshold in terms of $|F|=n^2$).**
IN `formal/WIP/Verified/Q43.lean` the predicate log2threshold Thm was introduced. 4.1 with replacement $n\\mapsto|F|$
and explicit `c1=27,680,440,320,000`:
$\\log_2 |F|\\le |F|/(c_1\\log_2^4 |F|)$.
This fixes the final form of the threshold in the grid parameter without hidden constants
(using $\\log_2$ base, `exp` does not participate).
See `formal/WIP/Verified/Q43.lean` (Q43_thm41_log2_threshold_c1_grid_explicit).
**Q43 (multiplied form of threshold).**
IN `formal/WIP/Verified/Q43.lean` threshold $\\log_2 |F|\\le |F|/(c_1\\log_2^4 |F|)$
rewritten into equivalent multiplicative form
$\\log_2 |F|\\cdot c_1\\log_2^4 |F|\\le |F|$ for $\\log_2 |F|\\ge 1$.
This is convenient for checking the $d$ mode without division (all estimates remain in the $\\log_2$ base).
See `formal/WIP/Verified/Q43.lean` (Q43_thm41_log2_threshold_c1_grid_iff_mul).
**Q43 (regime-d bundle + poly N/M bounds).**
In `formal/WIP/Verified/Q43.lean` the lemma `Q43_regime_d_ok_polyNM_bounds` is added.
It packages the log2^5 regime-d criterion (via `Q43_thm41_regime_d_ok_of_pow5`)
with the poly N/M log2 bounds from `Q43_polyNM_log2_bounds`.
This separates the regime-d hypothesis from the polynomial-size assumptions,
so the next step is to compare `log2 ((|F|)^C)` with `|F|/(c1 log2^4 |F|)`.
**Q43 (log2(|F|^C) bound).**
In `formal/WIP/Verified/Q43.lean` the lemma `Q43_log2_grid_pow_le_mul_succ` shows
`log2(|F|^C) <= (log2|F| + 1) * C` for `|F| = Q43_grid_size n`.
This uses only base‑2 `log2` and no `exp`, so the comparison reduces to a
polynomial factor in `log2|F|` before applying the log2^5 regime criterion.
Next step: use `log2|F| >= 1` (for `n >= 2`) to replace `log2|F| + 1` by `2 log2|F|`.
**Q43 (scaled log2^5 threshold for |F|^C).**
In `formal/WIP/Verified/Q43.lean` the lemma `Q43_thm41_log2_threshold_c1_grid_powC_of_scaled`
derives `log2(|F|^C) <= |F|/(c1 log2^4|F|)` from a scaled log2^5 criterion
`(2 log2|F| * C) * (c1 log2^4|F|) <= |F|`, still in base‑2 `log2`.
This isolates the remaining task to an explicit threshold `|F| >= n0(C)` and
the algebraic rewrite to the standard `2C·c1·log2^5|F| <= |F|`.
**Q43 (scaled log2^5 rewrite).**
In `formal/WIP/Verified/Q43.lean` the lemma
`Q43_thm41_log2_threshold_c1_grid_pow5_scaled_iff_simple` rewrites the scaled
condition into the compact form `2C·c1·log2^5|F| <= |F|` (still base‑2 `log2`).
This makes the remaining task purely a threshold choice `|F| >= n0(C)`.
Briefly: Tseitin - parities on the graph (odd sum of charges  unsatisfiability);
lower bounds through limited degree and expansion; Clique-Coloring -
incompatibility between cliques and coloring.
Note: Tseitin is often studied in algebraic systems (PC/Nullstellensatz).
Beame-Sabharwal 2000; review: Pitassi-Tzameret 2016, `../resources/downloads/pitassi_tzameret_2016_algebraic_proof_complexity.pdf`.
Status: For these EF families, lower estimates remain open; "Open Steps" below.
Enough: the superpolynomial EF-lower bound on such $tt$-formulas already gives the conclusion (via Pich-Santhanam).
More precisely: Theorem 9 requires the absence of proofs of length $2^{a n}$
(exponential bound), and for Cor. 2 is sufficiently superpolynomial
non-polynomiality EF+$w$.
We are talking about formulas of the form $tt(g_n,n^t,t(n))$ (template above).
Here $t(n)=1/2-1/2^{n/4}$ according to the setting from Pich-Santhanam.
The closer $t(n)$ is to $1/2$, the stronger the medium-complexity requirement (the smaller the acceptable correlation).
Reminder: $t(n)$ is the error threshold in the definition of $tt(f_n,s,t)$ (the proportion of inputs at which the circuit is errored).
- (L1) Lemma (EF coding). p-time $\mathrm{Enc}(n,\pi)$, $\mathrm{Len}(n,\pi)$.
  "there is an EF output $tt(g_n,n^t,t(n))$ of length $\le 2^{a n}$" $\Leftrightarrow$
  $\exists\pi\,\mathrm{Enc}(n,\pi)\wedge(\mathrm{Len}(n,\pi)\le 2^{a n})$.
  $\mathrm{Enc}$ checks local rules/axioms and the last line (Cook-Reckhow).
- (L2) Lemma (short EF $\Rightarrow$ approximation). p-time reduction $R$
  using code $\pi$ builds a circuit $C$ of size $n^t$ with an error $< t(n)$ in
  $\mathrm{poly}(|\pi|,n)$.
  Formalized in $\mathrm{S}^1_2$ and corresponding to $\mathrm{RedCorr}$/learning. *(Open step.)*
  Skeleton: $\mathrm{RedCorr}(n,C,y):=(y=R(n,C))\wedge \mathrm{Err}_{t(n)}(C,y)$.
  $\mathrm{Err}_{t(n)}$: $\exists S\le 2^n, |S|<t(n)2^n\wedge\forall x<2^n\ (x\notin S\to C(x)=g_n(x))$.
  Pich-Santhanam, Sec. 2.4/Thm 9; minimum (A)-(C) below.
- (L3) Lemma (contradiction). If $g_n\in\mathrm{E}$ is not approximated by circuits of size $n^t$ with error $< t(n)$, then L2 contradicts this.
**Formalization minimum (quantifiers).**
**Pattern.** $tt(g_n,n^t,t(n))$: no pattern of size $n^t$ approximates $g_n$ (error $\ge t(n)=1/2-1/2^{n/4}$).
Minimum: (A) $\mathrm{S}^1_2\vdash \exists n_0\,\forall n>n_0\ tt(h_{0,n},2^{n/4},t(n))$;
(B) $\mathrm{S}^1_2\vdash \forall n\,\forall C\,\exists y\le n^{O(1)}\ \mathrm{RedCorr}(n,C,y)$.
  (C) EF: $\exists a>0\,\forall n>n_0$ no EF output of length $\le 2^{a n}$
  for $tt(g_n,n^t,t(n))$. Thm 9/Cor. 2  schematic and uniform lower bounds.
**Definition (tt-formulas; Pich-Santhanam Sec. 2.4).** Let $f_n:\{0,1\}^n\to\{0,1\}$ be given by a truth table.
$tt(f_n,s)$: no circuit of size $s$ computes $f_n$ (need $>s$ circuits).
$tt(f_n,s,t)$: all circuits of size $s$ err on a fraction of inputs $\ge t$; these formulas are axioms EF+tt (see pattern $tt(g_n,n^t)$ above).

**Definition (formal $tt(f_n,s,t)$).** Let us fix the encoding of circuits of size $s$ by bitstrings $C$ of length $m(s)$ and a formula $\mathrm{Eval}(C,x)$ of polynomial size, calculating the output of circuit $C$ on a fixed $x$ (via variable gate values). For each $x\in\{0,1\}^n$ we set $e_x:=\mathrm{Eval}(C,x)\oplus f_n(x)$. Let $\mathrm{Count}_{\ge t2^n}(e)$ be a standard counting formula (for example, a sorting network), true if and only if $\sum_x e_x\ge t2^n$. Then
$$tt(f_n,s,t)\ :=\ \mathrm{Valid}_s(C)\ \to\ \mathrm{Count}_{\ge t2^n}\bigl((e_x)_{x\in\{0,1\}^n}\bigr).$$
Size $|tt|=\mathrm{poly}(2^n,s)$.

**Lemma 15.7.1a (Pich-Santhanam, Sec. 2.4.1).** In PS, the average complexity is fixed by $LB_{tt}(h,s(n),t(n)2^n)$ at scale $n\in\mathrm{LogLog}$; its propositional translation is $tt(f,s(n),t(n))$ with threshold $\mathrm{Count}_{\ge T(n)}$, where $T(n)=t(n)2^n$ is an integer. In particular, for $t(n)=1/2-1/2^{n/4}$ we have $T(n)=2^{n-1}-2^{3n/4}$, and this is the threshold used in (H1) and further in Theorem 9/Cor. 2.

**Barrier check (for 15.7.1a).**
- Relativization: translation of $LB_{tt}\mapsto tt$ is preserved during oracle gates; This is purely a syntactic step.
- Natural proofs: fixing the threshold $T(n)$ does not avoid the RR barrier if the proof of medium complexity is constructed via constructive/large-scale properties.
- Algebrization: the step does not algebraize; This is just the coding of the counter.

**Lemma 15.7.1b (scale $n\in\mathrm{LogLog}$ and threshold rounding).** In PS (Sec. 2.4.1) $tt(f,s(n),t(n))$ is obtained by translating $LB_{tt}(h,s(n),t(n)2^n)$ with the substitution of a fixed constant $x=2^{2^n}$ (i.e. $n=||x||$), which makes the truth table $f$ "accessible" and preserves the $\Pi^b_1$-form. If $t(n)2^n$ is not an integer, the threshold in $\mathrm{Count}_{\ge T(n)}$ can be taken as $T(n):=\lceil t(n)2^n\rceil$ (or $\lfloor\cdot\rfloor$); this changes the formula only by $\pm1$ in count and does not affect the use in (H1)/Thm 9.

**Lemma 15.7.1c (division $n/4$ and implementation $\mathrm{Count}_{\ge T}$).** In PS the parameters are written as $2^{||x||/4}$ and $1/2-1/2^{||x||/4}$ (Sec. 2.4.2, Def. 3), that is, in fact the integer $r(n)=\lfloor is used n/4\rfloor$.  $t(n)=1/2-1/2^{r(n)}$ 
$$T(n)=t(n)2^n=2^{n-1}-2^{n-r(n)}\quad(\text{with }4\mid n\text{ this is }2^{n-1}-2^{3n/4}).$$
You can either restrict yourself to $n$ being multiples of $4$ (by adding a condition to (H1)), or accept $r(n)=\lfloor n/4\rfloor$ without changing the output. The formula $\mathrm{Count}_{\ge T}$ can be implemented by a standard sorting network or an adder using $\mathrm{poly}(2^n)$ (this is sufficient for EF and for the scale $n\in\mathrm{LogLog}$).

**Lemma 15.7.1d (counter size).** Let $N=2^n$ be the number of bits of $(e_x)_x$. There is a Boolean circuit of size $O(N\log N)$ and depth $O(\log N)$ that computes the sum $\sum_x e_x$ in binary form (for example, a binary adder tree) and then checks $\sum_x e_x\ge T$ with a comparator. Therefore, $\mathrm{Count}_{\ge T}$ can be wired into $tt(f,s,t)$ with a circuit of size $\mathrm{poly}(N)=\mathrm{poly}(2^n)$.

**Note (3CNF for $\mathrm{Count}_{\ge T}$).** If you need to have exactly a CNF/3CNF subformula, then the scheme from Lemma 15.7.1d can be translated into 3CNF with $O(N\log N)$ clauses using standard Tseitin encoding (see Section 16.80).

**Barrier check (for 15.7.1b-15.7.1d).**
- Relativization: fixing $x=2^{2^n}$ and rounding - the syntax is relativized.
- Natural proofs: does not bypass the RR barrier (pure coding).
- Algebrization: does not algebraize.

**Lemma 15.7.1 (equivalence).** $tt(f_n,s,t)$ is a tautology $\iff$ any circuit of size $s$ fails on a fraction of inputs $\ge t$.

*Proof.* ($\Rightarrow$) Let there be a circuit $C$ of size $s$ with error $<t$. Let's substitute its code into $C$ and the agreed gate values; then $\mathrm{Valid}_s(C)=1$, but the counter produces $0$, the formula is false. ($\Leftarrow$) If the formula is false on some assignment, then $C$ is valid and $\sum_x e_x<t2^n$, then a scheme with error $<t$ was found. $\square$

**Where used.** Conjecture (H1) of Section 15.7 takes $s=2^{n/4}$ and $t(n)=1/2-1/2^{n/4}$ and states that $tt(h_{0,n},s,t(n))$ is a tautology for all large $n$. These formulas are included in the axiom scheme $\mathrm{EF}+tt(h,s,t)$ and are used as a premise in Theorem 8/9 (Pich-Santhanam) to derive the scheme lower bounds.

**Barrier check.**
- Relativization: the definition is completely relativized (oracle gates can be added), so that by itself does not give a non-relativizing step.
- Natural proofs: a proof of average complexity of explicit $h_0$ via a constructive/large-scale property will fall under the Razborov-Rudich barrier if PRFs exist.
- Algebrization: the step does not algebraize the problem; translation into algebraic form does not remove the requirements for non-algebrizing techniques.

**Lemma 15.7.2 (unpacking S$^1_2$-premises).** Let us fix an explicit $h_0\in\mathrm{E}$ with the evaluation predicate $\mathrm{Eval}_{h_0}(n,x,b)$, as well as an explicit p-time reduction of $R$ with the graph predicate $\mathrm{Graph}_R(n,C,y)$ and the estimate $|y|\le p(n)$. Then the premises from Pich-Santhanam can be written as $\forall\Pi^b_1$-sentences:

1) (H1$_\Pi$) $\exists n_0\,\forall n>n_0\,\forall C\le m(2^{n/4})\;
\bigl(\mathrm{Valid}_{2^{n/4}}(C)\to \mathrm{Count}_{\ge t(n)2^n}((e_x)_x)\bigr)$,
where $e_x:=\mathrm{Eval}(C,x)\oplus \mathrm{Eval}_{h_0}(n,x,1)$.

2) (H2$_\Pi$) $\forall n\,\forall C\le m(n)\;\mathrm{RedCorr}(n,C,R(n,C))$,
where $R(n,C)$ is defined by $\mathrm{Graph}_R(n,C,y)$.

*Proof (sketch).* In (H1$_\Pi$) all quantifiers are bounded,
$\mathrm{Eval}_{h_0}$ is specified by bounded-check calculation for $2^{O(n)}$,
and $\mathrm{Count}_{\ge}$ is implemented by a standard counting scheme; it gives
class formula $\Pi^b_1$ under the outer $\exists n_0$. In (H2$_\Pi$) replacement
$\exists y$ on $y=R(n,C)$ makes the formula $\Pi^b_1$, and in $\mathrm{S}^1_2$
the totality p-time $R$ is transported, therefore (H2$_\Pi$) $\Rightarrow$
$\forall n\,\forall C\,\exists y\,\mathrm{RedCorr}(n,C,y)$. $\square$

**Lemma 15.7.2a (encoding $\mathrm{Eval}_{h_0}$ and $\mathrm{Graph}_R$).** In the PS formalization (Sec. 2.2/2.4), the predicates $\mathrm{Eval}_{h_0}$ and $\mathrm{Graph}_R$ can be considered PV-formulas with polynomial length constraints: if $h_0\in\mathrm{E}$, then at the scale $n\in\mathrm{LogLog}$ (that is, $\exists x,\ n=||x||$) the calculation of $h_0$ in $2^{O(n)}$ time becomes $\mathrm{poly}(|x|)$ and admits the PV definition $\mathrm{Eval}_{h_0}(n,x,b)$; if $R$ is a p-time reduction, then its graph $\mathrm{Graph}_R(n,C,y)$ is given by a PV formula with the constraint $|y|\le p(n)$ for some polynomial $p$.

**Barrier check (for 15.7.2a).**
- Relativization: the step is purely syntactic (PV-definable) and is relativized.
- Natural proofs: not applicable (no circuit complexity statement).
- Algebrization: not applicable (no algebraic transformation).

**Lemma 15.7.2b (circuit code length and $\mathrm{Valid}_s$).** Let us fix the standard list encoding of a Boolean circuit of size $s$ with fan-in $2$: for each vertex $i$ we store the gate type and two input indices $<i$ (plus input variables and constants). Then the code length is $m(s,n)=O(s\log s+n\log s)$, and for $n\le s$ we can take $m(s)=O(s\log s)$. The predicate $\mathrm{Valid}_s(C)$ that checks the correctness of indices/types is a $\Delta^b_0$-formula (and therefore PV-computable), which justifies the constraint of $C\le m(s)$ in (H1$_\Pi$)/(H2$_\Pi$). In particular, for $s=2^{n/4}$ we have $m(s)=2^{O(n)}$.

**Barrier check (for 15.7.2b).**
- Relativization: encoding and checking the correctness of the scheme is a purely syntactic step.
- Natural proofs: not applicable.
- Algebrization: not applicable.

**Note (padding; the meaning of the constraint $C\le m(s)$).** In (H1$_\Pi$)/(H2$_\Pi$) the quantifier over $C$ is read as a bounded quantifier over the code of the circuit of length $\le m(s)$ (equivalently, over the number $C<2^{m(s)}$). This restriction does not exclude any scheme of size $\le s$: with gate-list encoding, you can always reduce the code to a fixed length $m(s)$ (for example, by adding dummy entries/zeros to the list of $s$ gates) without changing the decoded scheme. Therefore, all meaningful restrictions on $C$ go through $\mathrm{Valid}_s(C)$, and $C\le m(s)$ only makes the quantifier bounded (see Section 16.79).

**Lemma 15.7.2c (evaluation $\mathrm{Eval}(C,x)$).** For gate-list encoding from Lemma 15.7.2b, the function $\mathrm{Out}(C,x)$, which calculates the output of circuit $C$ at input $x$, is a PV function (computed in $\mathrm{poly}(s)$ steps). Then the predicate $\mathrm{Eval}(C,x,b):\equiv (\mathrm{Out}(C,x)=b)$ is a $\Delta^b_0$-formula. The propositional translation can use $O(s)$ of auxiliary variables for gate values and $O(s)$ of local constraints, so that the size of the formula $\mathrm{Eval}(C,x)$ is $\mathrm{poly}(s)$ (and hence $|tt|=\mathrm{poly}(2^n,s)$).

**Barrier check (for 15.7.2c).**
- Relativization: The circuit output estimate is relativized.
- Natural proofs: not applicable.
- Algebrization: not applicable.

**Where the power-up is hidden.**
- (H1$_\Pi$) is the a.e.-hardness (for all large $n$), and not the i.o.-variant,
and the function $h_0$ is fixed and explicit.
- (H2$_\Pi$) requires a **fixed** reduction of $R$ and provable totality
in $\mathrm{S}^1_2$; without $R$ the formula becomes $\Sigma^b_2$.

**Barrier check.**
- Relativization: both formulas are relativized when adding oracle gates.
- Natural proofs: (H1$_\Pi$) with a constructive/large proof falls under the RR barrier (with PRF).
- Algebrization: formulas do not remove the algebrization barrier; non-algebraizing ideas are needed.

**Definition (axiom scheme EF + tt(h,s,t); Pich-Santhanam Sec. 2.4).** Let $h\in\mathrm{E}$ and the functions $s(2^n),t(2^n)$ be as follows.
For all large $n$, any circuit of size $s(2^n)$ errs by a fraction of $\ge t(2^n)$ by $h_n$.
Then $\mathrm{EF}+tt(h,s,t)$ is EF with axioms $\{tt(h_n,s(2^n),t(2^n)):\n\ge n_0\}$.

**Definition (anticheckers).** For the function $f$ and $s$ the set
$A_n^{f,s}\subseteq\{0,1\}^n$ is called antichecker if
$|A_n^{f,s}|=\mathrm{poly}(s)$.
Any circuit of this size fails at input from $A_n^{f,s}$.
For functions $f$ that are difficult for circuits of size $s^3$ (for $s\ge n^3$), anticheckers exist.
Average difficulty $f$ gives anticheckers; Pich-Santhanam, Sec. 3 (`../resources/downloads/pich_santhanam_2023_ef_lower_bounds.pdf`).
Thm 7: "feasible anticheckers" are formalized in terms of EF+$w$ and give schematic lower bounds when EF is non-polynomial (averagecase premise).

**Theorems 7-9 (Pich-Santhanam 2023, Sec. 3-5; cited).**
**Dependency diagram (compressed).**
- (H1) $\mathrm{S}^1_2$ proves the average complexity of $h_0\in\mathrm{E}$: $tt(h_{0,n},2^{n/4},t(n))$ *(status: not proven for explicit $h_0$).*
- (H2a) $\mathrm{S}^1_2$ formalizes the reduction of $\neg\exists\mathrm{OWF}\Rightarrow$ learning (via $\mathrm{RedCorr}$).
- (H2b) $\mathrm{S}^1_2$ formalizes the $\mathrm{NP}\not\subseteq\mathrm{P/poly}\Rightarrow$ OWF reduction (alternative).
- (H3a) EF+tt has lower bounds $2^{a n}$ on $tt(g_n,n^t,t(n))$ (pattern above) *(status: open).*
- (H3b) EF (or EF+$w$) not p-bounded (option Thm 7/Cor. 2) *(status: open).*
Then: (H1)+(H2a)+(H3a) $\Rightarrow$ $\mathrm{SAT}\notin\mathrm{Circuit}[n^k]$ (Thm 9; Cor. 2 gives the uniform version).
(H1)+(H2b)+(H3b) $\Rightarrow$ $\mathrm{SAT}\notin\mathrm{P/poly}$ (Thm 8).
Note: EF lower bounds by themselves are not sufficient for $\mathrm{NP}\ne\mathrm{coNP}$ without p-optimality.

**Open steps (checklist).**
- (O1) Prove the average complexity $h_0\in\mathrm{E}$: $tt(h_{0,n},2^{n/4},t(n))$.
- (O2) Prove EF lower bounds $2^{a n}$ for $tt(g_n,n^t,t(n))$ (or non-polynomiality EF/EF+$w$ on explicit tautologies).

Status: (O1) - standard conjecture about average complexity in $\mathrm{E}$ (bounds have not been proven for explicit functions); (O2) is an open EF task.

Barrier context: Natural Proofs and Algebrization limit circuit techniques;
strong EF lower bounds expect non-relativizing/non-natural ideas.

**Definition (option with advice).** $w_{n,k,u}(f)$: $C$ circuits read like codes
$O(n^k)$ time algorithms with advice of length $u(n)$ (p-time, $u(n)\le n^k$).
$W_{n,k,u}(f)$ -- $\forall\Pi^b_1$-formalization "for all $n>n_0$ the formulas $w_{n,k,u}(f)$ are tautologies."
$\mathrm{Time}[n^k]/u(n)$ is a class of languages that can be solved by such algorithms.

Note: EF+tt captures the hardness of a particular $h$, while EF+$w$ encodes lower bounds against $\mathrm{Time}[n^k]/u(n)$.
Thm 9 uses EF+tt, Cor. 2 -- EF+$w$. See the list of "Open Steps" below.

**Notation.** $\mathrm{EF}+w_{k,u}(f)$ means EF with axiom circuit
$\{w_{n,k,u}(f): n\ge n_0\}$ (similar to the definition of $\mathrm{EF}+tt(h,s,t)$ above).

**Consequence (Pich-Santhanam 2023, Cor. 2).**
Let $k\ge 1$ and $u$ p-time, $u(n)\le n^k$.

1) If there is a p-time $f$ such that for all large $n$ $w_{n,k,u}(f)$ are tautologies, and the system $\mathrm{EF}+w_{k,u}(f)$ is not p-bounded,
then $\mathrm{SAT}\notin\mathrm{Time}[n^{\Omega(k)}]/u(n)$ of infinitely many $n$.

2) If $\mathrm{S}^1_2\vdash W_{n,k,u}(f)$ and EF is not p-bounded, then the same conclusion.

**Comparison of systems (briefly).**
|  |  | Comment |
|---|---|---|
| Frege | fixed axiom schemes + rules | different options are polynomially equivalent |
| EF | Frege + extensions $p\leftrightarrow\psi$ | one of the most powerful standard systems |
| AC0-Frege | Frege with depth $d$ | significantly weaker than EF; lower bounds are known |
| CP | linear inequalities over $\{0,1\}$ | convenient for counting arguments (`../resources/downloads/buss_cutting_planes_notes.pdf`) |

### 15.8. PHP has a polynomial refutation in CP (complete proof)

Here you can see "why" the resolution is weak: PHP is exponentially difficult
for a resolution, but is simply refuted in CP due to the countable
(linear) argument.

Consider $m=n+1$ pigeons and $n$ minks, variables $x_{i,j}\in\{0,1\}$.

Instead of the CNF encoding from Section 15, we use an equivalent (at $\{0,1\}$) system of linear inequalities:

1) *(a dove is sitting somewhere)* for each $i\in\{1,\dots,m\}$:
$$\sum_{j=1}^n x_{i,j}\ \ge\ 1.$$

2) *(not together)* for each $j\in\{1,\dots,n\}$:
$$\sum_{i=1}^m x_{i,j}\ \le\ 1,$$
that is equivalent
$$-\sum_{i=1}^m x_{i,j}\ \ge\ -1.$$

Note: pairwise CNF clauses $(\neg x_{i,j}\lor\neg x_{i',j})$ by $\{0,1\}$
are equivalent to the constraint $\sum_i x_{i,j}\le 1$ ("at most one one per column").
$(\Leftarrow)$ is obvious, and if $\sum_i x_{i,j}\ge 2$, then there are $i\ne i'$ with $x_{i,j}=x_{i',j}=1$, and the clause is false.

**Theorem 15.8.** There is a CP refutation of $\mathrm{PHP}^{n}_{n+1}$ of size $\mathrm{poly}(n)$.

*Proof.* Let us denote $S:=\sum_{i=1}^m\sum_{j=1}^n x_{i,j}$.

Let us add inequalities (1) over all $i$ (addition rule CP): we obtain
$$S\ \ge\ m\ =\ n+1.$$ 

Let us add inequalities (2') over all $j$ (in the form with $\ge$):
$$-S\ \ge\ -n.$$ 

Adding these two inequalities, we obtain $0\ge 1$ (equivalent to $-1\ge 0$),
that is, a contradiction. This means that the system does not have 0/1solutions, and this is
CP refutation.

*Size estimate.* We use $O(n)$ additions, each inequality has
$O(n)$ ,     $\mathrm{poly}(n)$. $\square$
