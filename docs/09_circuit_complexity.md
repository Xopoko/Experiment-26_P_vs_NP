## 9. Circuit complexity: basic definitions
Also IPS and communication with VP vs VNP - in section 15.7.
IPS works with algebraic circuits, not Boolean ones.
Note: in algebraic schemes the size is the number of operations $+$/\times,
in Boolean - the number of logical elements.
Mini-definitions (algebraic classes):
VP - families of polynomials of pbounded degree, computable by polynomial
algebraic schemes;
VNP - families of the form $f_n(x)=\sum_{y\in\{0,1\}^{m(n)}} g_n(x,y)$
with $g_n\in\mathrm{VP}$ (Valiant).
We fix the field $\mathbb{F}$ (for example, $\mathbb{Q}$ or $\mathbb{F}_p$);
VP/VNP definitions depend on the selected field.
Examples: $\det$ in VP, $\mathrm{perm}$ VNP is complete (Valiant 1979).
Status: VP=VNP - open issue; superpolynomial lower bounds are known only for limited models.
See review: Saptharishi 2016 (`../resources/downloads/saptharishi_2016_arithmetic_circuit_survey.pdf`).
For the technique of lower bounds in an algebraic model: Saptharishi 2016 (review of methods).

Here we fix a minimal language for talking about lower bounds for Boolean circuits.

**Boolean function/family.** Consider the family $f=\{f_n\}_{n\ge 1}$, where $f_n:\{0,1\}^n\to\{0,1\}$.

**Circuit.** Boolean circuit $C$ - directed acyclic graph
with inputs $x_1,\dots,x_n$ and AND/OR/NOT elements, calculating a Boolean function.

**Size** $|C|$ -- number of logical elements; **depth** $\mathrm{depth}(C)$ is the length of the maximum path from input to output.

**Unlimited fan-in.** In AC0 models we allow AND/OR with arbitrary
number of inputs (unbounded fan-in).
It is convenient to consider negations as standing only at inputs; pushing NOT
according to De Morgan's laws, it maintains a constant depth with an increase by a constant.

**Class P/poly (informal).** Language in $\mathrm{P/poly}$, if exists
a family of polynomial-sized Boolean circuits that compute it, or
equivalent: there is a deterministic polynomial algorithm
with a polynomial advice $a_n$ of length $n^{O(1)}$ depending only on $n$.

**Notation (SIZE).** $\mathrm{SIZE}(s(n))$ are languages recognized by a family of Boolean circuits of size $O(s(n))$ (unevenly).

**Notation (Circuit).** $\mathrm{Circuit}(s(n))$ is the same class as $\mathrm{SIZE}(s(n))$.
Used interchangeably with $\mathrm{SIZE}(s)$ (Section 15.7, Cor. 2).

See Section 8 and Section 15.7 (Cor. 2) for connections to lower bounds.

**Definition (Time[n^k]/u(n), roughly).** These are the classes of languages solved
deterministic algorithms in $O(n^k)$ with advice of length $u(n)$,
depending only on $n$.

See Section 15.7 (Cor. 2) for consequences under SAT and the $w_{n,k,u}(f)$ scheme.

**Class AC0.** Family $f$ lies in AC0 if constant $d$ exists
and a family of circuits $\{C_n\}$ such that $\mathrm{depth}(C_n)\le d$,
size $|C_n|\le n^{O(1)}$, and $C_n(x)=f_n(x)$ for all $x\in\{0,1\}^n$.

**DNF/CNF as a special case.** DNF - depth scheme of 2 types OR from AND terms; CNF - AND from OR clauses.

The problem of circuit lower bounds: prove that for an explicit family of functions
(e.g. SAT/CLIQUE/PARITY) *any* representative from the selected class
must be large in size/depth.

**Monotone schemes.** The function $f$ is monotone if $x\le x'$ is coordinatewise
implies $f(x)\le f(x')$. For monotonic $f$, consider schemes without NOT
(AND/OR only); Let's denote the minimum size by $L_f^+$.
Obviously $L_f\le L_f^+$.

**Theorem 9.1 (Razborov, 1985, cited).** Let $f_{m,s}$ be a function
on $n_m=\binom m2$ bits, equal to 1 if and only if the graph is on $m$
vertices contains a clique of size $\ge s$. Then:

- for $s=\lfloor \tfrac14\ln m\rfloor$ we have $L_{f_{m,s}}^+\ge m^{C\ln m}$ for some constant $C>0$;
- for fixed $s$ we have $L_{f_{m,s}}^+\ge \Omega\big(m^s/(\ln m)^{2s}\big)$.

Note: this is the lower bound in the **monotonic** model (without NOT),
and therefore does not itself provide lower bounds for general Boolean circuits.

**Modern context.** Grewal-Kumar (2024) show that the series AC^0[p]-
lower bounds carry over to the extended class GC^0[p], giving
exponential lower bounds for MAJ.
