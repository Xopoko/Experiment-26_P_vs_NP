## 6. Reduction of 3SAT $\le_m^p$ CLIQUE (proof + verification on small cases)

**Problem CLIQUE (decision).** Input: undirected graph $G=(V,E)$ and number $k$. Question: Is there a clique of size $\ge k$?

**Lean skeleton:** CNF/3CNF/SAT in `formal/PvNP/Core/SAT.lean`, base graph and clique - `formal/PvNP/Core/Graph.lean`, definition 3SAT->CLIQUE - `formal/PvNP/Core/ReductionsSAT.lean`.
Correctness is the goal for formalization in Lean (not yet proven in `formal/`).

**Theorem 6.1.** 3SAT $\le_m^p$ CLIQUE.

*Construction.* Let a 3CNF formula $\varphi$ have $m$ clauses $C_1,\dots,C_m$, each a clause of three literals. We build the graph $G$:

- Vertices: one vertex for each literal in each clause, i.e. $v_{i,\ell}$ for $\ell\in C_i$.
- Edges: connect $v_{i,\ell}$ and $v_{j,\ell'}$ (where $i\ne j$)
  if and only if the literals are **compatible**: are not
  mutually exclusive, i.e. do not have the form $x$ and $\neg x$ for one variable.

Output: pair $(G,k)$ where $k=m$.

*Correctness.*

- If $\varphi$ is satisfiable, choose a true literal $\ell_i$ in each clause.
  These literals are compatible (otherwise the assignment would make one of them false).
  Then for any $i\ne j$ the vertices $v_{i,\ell_i}$ and $v_{j,\ell_j}$ are connected;
  we obtain a clique of $m$ vertices.

- If $G$ has a clique of size $m$, then it takes one vertex from each group
  $\{v_{i,\ell}:\ell\in C_i\}$ (there are no edges inside the clause), i.e. selects $\ell_i$.
  The compatibility of all pairs means that there is no pair of the form $x$ and $\neg x$.
  Let's construct an assignment consistent with the selected literals (the rest are arbitrary).
  Then each $C_i$ is satisfied with the chosen $\ell_i$, which means the entire formula is satisfied.

*Complexity.* The graph has $3m$ vertices and $O(m^2)$ potential edges; construction takes polynomial time.

$\square$

**Lemma 6.2.** 3SAT $\in\mathrm{NP}$.


*Proof.* Certificate - assignment of Boolean values to variables.
The verifier checks the truth of each clause in $O(|\varphi|)$ time.
$\square$


**Corollary 6.3.** If SAT is NP-complete (Cook-Levin), then 3SAT is NP-complete.

*Proof.* From Theorem 5.1 we have SAT $\le_m^p$ 3SAT.
Since 3SAT $\in\mathrm{NP}$, then 3SAT is NP-hard and belongs to NP,
means NPcomplete. $\square$

**Lemma 6.4.** CLIQUE $\in\mathrm{NP}$.

*Proof.* Certificate is a list of $k$ vertices.
The verifier checks in $O(k^2)$ that all pairs are connected by an edge.
$\square$

**Corollary 6.5.** CLIQUE is NPcomplete.

*Proof.* By Theorem 6.1 we have 3SAT $\le_m^p$ CLIQUE.
By Corollary 6.3, problem 3SAT is NPcomplete. With Lemma 6.4 (CLIQUE $\in\mathrm{NP}$)
we obtain NP-completeness CLIQUE. $\square$
