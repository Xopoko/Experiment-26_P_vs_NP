## 3. Basic inclusions (complete proofs)

**Lemma 3.1.** $\mathrm{P}\subseteq\mathrm{NP}$.

*Proof.* A deterministic machine is a special case of a non-deterministic machine (without branches).
If $L$ is solved deterministically in polynomial time, then it is solved nondeterministically in the same time. $\square$

**Lemma 3.2.** $\mathrm{NP}\subseteq\mathrm{PSPACE}$.

*Proof (classical).* Let $L\in\mathrm{NP}$ be recognized by the NMT $N$ for $n^k$.
Consider the graph of configurations $G_x$ for input $x$: vertices are configurations $N$ on $x$, edge is one computation step.
The number of configurations is $\le 2^{O(n^k)}$, but each configuration takes up $O(n^k)$ of memory.

A deterministic machine checks the path from the starting configuration to the receiving configuration using DFS along the path length
(or Savich reachability for NLSPACE(log_22) as a general pattern).
You can iterate branches "in depth", storing the current configuration and the step counter up to $n^k$.
This requires $O(n^k)$ memory for configuration and $O(\log_2 n)$ for counters, i.e.  .
Therefore, $L\in\mathrm{PSPACE}$. $\square$

**Lemma 3.3.** If $\mathrm{P}=\mathrm{NP}$, then $\mathrm{NP}=\mathrm{coNP}$.

*Proof.* From $\mathrm{P}=\mathrm{NP}$ it follows $\mathrm{NP}=\mathrm{P}$.
$\mathrm{P}$ is closed by complement: if $M$ solves $L$ in polynomial time, then
a machine changing accept/reject solves $\overline{L}$ in the same time.
This means $\overline{L}\in\mathrm{P}=\mathrm{NP}$ for any $L\in\mathrm{NP}$, that is, $\mathrm{coNP}\subseteq\mathrm{NP}$.
The reverse inclusion $\mathrm{NP}\subseteq\mathrm{coNP}$ is symmetric. $\square$
