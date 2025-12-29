## 5. Lemma: SAT $\le_m^p$ 3SAT (complete proof)

We will encode the CNF formula $F$ as a conjunction of clauses (disjuncts) from literals. Literal is the variable $x_i$ or its negation $\neg x_i$.

**Lean skeleton:** syntactic definitions of CNF/3CNF and SAT are specified in `formal/PvNP/Core/SAT.lean` (encoding into bitstrings has not yet been formalized).
The definition of the SAT->3SAT conversion is specified in `formal/PvNP/Core/ReductionsSAT.lean`;
the "result - 3CNF" property is formalized as `satTo3Sat_is3cnf` right there.
Equivalence is a goal for formalization in `formal/PvNP/Core/ReductionsSAT.lean` (not yet proven in Lean).

**Theorem 5.1.** There is a polynomial computable function $T$, which
using a CNF formula $F$ constructs a 3CNF formula $T(F)$ such that $F$ is satisfiable
if and only if $T(F)$ is satisfiable.

*Construction.* Let $F=\bigwedge_{j=1}^m C_j$, where $C_j$ is the clause of $k_j$ literals.

1) If $k_j=1$, then $C_j=(\ell_1)$ is replaced by $(\ell_1\lor\ell_1\lor\ell_1)$.

2) If $k_j=2$, then $C_j=(\ell_1\lor\ell_2)$ is replaced by $(\ell_1\lor\ell_2\lor\ell_2)$.

3) If $k_j=3$, leave it as is.

4) If $k_j>3$ and $C_j=(\ell_1\lor\ell_2\lor\cdots\lor\ell_{k_j})$, enter
new variables $y_1,\dots,y_{k_j-3}$ and replace $C_j$
on the conjunction of $k_j-2$ triliteral clauses:

$$(\ell_1\lor\ell_2\lor y_1)\ \wedge\ (\neg y_1\lor\ell_3\lor y_2)\ \wedge\ \cdots
(\neg y_{k_j-4}\lor\ell_{k_j-2}\lor y_{k_j-3})
\ \wedge\ (\neg y_{k_j-3}\lor\ell_{k_j-1}\lor\ell_{k_j}).$$

Let us define $T(F)$ as the conjunction of transformed clauses for all $j$.

*Correctness (equisatisfiability).* It is enough to check $C_j$ for each clause.

- The $k_j\le 3$ cases obviously preserve satisfiability: the replacement adds duplicate literals.

- Let $k_j>3$. Let us denote the resulting chain of clauses as $D_1\wedge\cdots\wedge D_{k_j-2}$.

($\Rightarrow$) Let $C_j$ be true on assignment $x$, and $\ell_t$ be true.
If $t\le 2$, we set all $y_i=\mathrm{false}$.
If $t>2$, set $y_i=\mathrm{true}$ for $i< t-2$ and $y_i=\mathrm{false}$ for $i\ge t-2$.
Then in each $D_i$ at least one literal is true; the chain is feasible.

($\Leftarrow$) Let the chain be satisfiable, but all $\ell_1,\dots,\ell_{k_j}$ are false.
Then from $D_1=(\ell_1\lor\ell_2\lor y_1)$ it follows that $y_1=\mathrm{true}$,
from $D_2=(\neg y_1\lor\ell_3\lor y_2)$ - $y_2=\mathrm{true}$, and so on,
we get $y_{k_j-3}=\mathrm{true}$.
The last clause $D_{k_j-2}$ becomes false - a contradiction.
This means that at least one $\ell_t$ is true, that is, $C_j$ is true.

Thus, $C_j$ is feasible. $\iff$ the corresponding 3CNF substitution is feasible.
By conjunction over all $j$ we obtain $F$ is satisfiable $\iff T(F)$ is satisfiable.

*Complexity.* Size increases linearly with the total length of the clauses
(for a clause of length $k$, $k-2$ clauses and $k-3$ new variables are created).
This means $T$ is computable in polynomial time.

$\square$
