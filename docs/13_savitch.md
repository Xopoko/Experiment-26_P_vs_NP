## 13. Savich's theorem: NSPACE  SPACE (complete proof)

**Definition (SPACE/NSPACE).** For the function $s(n)$ class
$\mathrm{SPACE}(s(n))$ -- languages solved by deterministic MT,
using $O(s(n))$ work cells at the input of length $n$.
Similarly $\mathrm{NSPACE}(s(n))$ - for non-deterministic MT.

Working memory does not include input tape (input is read only).

**Theorem 13.1 (Savitch).** For any $s(n)\ge \log_2 n$ is true
$$\mathrm{NSPACE}(s(n))\subseteq\mathrm{SPACE}(s(n)^2).$$

*Proof.* Let the language $L$ be recognized by a non-deterministic MT $N$
using $s(n)$ memory. Let us fix an input $x$ of length $n$.

Consider the **configuration graph** $G_x$: vertices are configurations $N$
at input $x$ (contents of working tapes, head positions, state),
and an edge $c\to c'$ exists if $N$ can go from $c$ to $c'$ in one step.

Since memory is limited by $s(n)$, the length of the configuration description is
$O(s(n))$, and the number of configurations is limited
$$|V(G_x)|\le 2^{O(s(n))}=:M.$$

Input $x$ is accepted if and only if a path exists in $G_x$
from the starting configuration $c_{\mathrm{start}}$ to some receiving configuration
configuration $c_{\mathrm{acc}}$.

The key subalgorithm is the procedure $\mathrm{REACH}(c_1,c_2,\ell)$:
whether there is a path from $c_1$ to $c_2$ of length $\le \ell$.

- Base: $\ell=0$ - the answer is "yes" if and only if $c_1=c_2$.
- Transition: for $\ell>0$ we set $m=\lceil \ell/2\rceil$ and check
$$\exists c\in V(G_x):\ \mathrm{REACH}(c_1,c,m)\ \wedge\ \mathrm{REACH}(c,c_2,m).$$

If a path of length $\le \ell$ exists, then there is a vertex $c$ in its middle,
splitting the path into two parts of length $\le m$.
Conversely, if both halves exist, concatenating them gives a path of length
$\le 2m\ge\ell$.

To solve reachability in $G_x$, it is enough to check
$\mathrm{REACH}(c_{\mathrm{start}},c_{\mathrm{acc}},M)$ for all $c_{\mathrm{acc}}$.

**Memory estimate.** One configuration is encoded in $O(s(n))$ bits.
In each recursive call we store $(c_1,c_2,\ell)$ and the current candidate $c$ -
this is $O(s(n))$ of memory. The recursion depth is $O(\log_2 M)=O(s(n))$,
this means the total memory is $O(s(n)\cdot s(n))=O(s(n)^2)$.

Thus, reachability in $G_x$ is solved deterministically in
$O(s(n)^2)$ of memory, and therefore $L\in\mathrm{SPACE}(s(n)^2)$. $\square$

**Corollary 13.2.** $\mathrm{NPSPACE}=\mathrm{PSPACE}$.

*Proof.* Obviously $\mathrm{PSPACE}\subseteq\mathrm{NPSPACE}$.
Conversely, we apply Theorem 13.1 to $s(n)=n^k$ and get
$\mathrm{NPSPACE}\subseteq\mathrm{PSPACE}$. $\square$

**Corollary 13.3.** $\mathrm{NP}\subseteq\mathrm{PSPACE}$.

*Proof.* $\mathrm{NP}\subseteq\mathrm{NPSPACE}$
(nondeterministic polynomial time uses at most
polynomial memory), and then Corollary 13.2. $\square$
