## 6.6. Two more NP-complete problems: INDEPENDENT SET and VERTEX COVER

**INDEPENDENT SET (IS).** Input: undirected graph $G=(V,E)$ and number $k$.
Question: is there an independent set of vertices of size $\ge k$?

**VERTEX COVER (VC).** Input: undirected graph $G=(V,E)$ and number $k$.
Question: Is there a vertex cover of size $\le k$
(the set of vertices incident to each edge)?

**Lemma 6.6.1.** $(G,k)\in\mathrm{CLIQUE}$ if and only if
when $(\overline{G},k)\in\mathrm{IS}$, where $\overline{G}$ is the complement of the graph $G$.

*Proof.* $S\subseteq V$ is a clique in $G$ $\iff$ between any two different vertices from $S$ is an edge.
Equivalently: there is **no** edge between any two vertices in $S$ in $\overline{G}$, which means $S$ is independent. $\square$

**Lemma 6.6.2.** For any graph $G=(V,E)$ the set $S\subseteq V$
is independent if and only if $V\setminus S$
is a vertex covering.

*Proof.* If $S$ is independent, then no edge has both ends in $S$,
this means that each edge ends at $V\setminus S$, that is, $V\setminus S$ is a vertex cover.
Conversely, if $C$ is a vertex cover, then there is no edge in $V\setminus C$ (otherwise it is uncovered),
means $V\setminus C$ is independent set. $\square$

**Corollary 6.6.3.** $(G,k)\in\mathrm{IS}$ if and only if $(G,|V|-k)\in\mathrm{VC}$.

*Proof.* By Lemma 6.6.2, the existence of an independent set of size $\ge k$
is equivalent to having a vertex cover of size $\le |V|-k$. $\square$

**Lemma 6.6.4.** IS $\in\mathrm{NP}$ and VC $\in\mathrm{NP}$.

*Proof.* IS: certificate is a list of $k$ vertices; we check that there is no edge inside the list.
VC: certificate - a list of $k$ vertices; we check that each edge has an end in the list,
which is done in $O(|E|)$ time. $\square$

**Corollary 6.6.5.** IS and VC are NPcomplete.

*Proof.* CLIQUE is NPcomplete (Corollary 6.5).
By Lemma 6.6.1 we have CLIQUE $\le_m^p$ IS (construction of $\overline{G}$).
By Corollary 6.6.3 we have IS $\le_m^p$ VC.
With Lemma 6.6.4 we obtain NP-completeness of IS and VC. $\square$
