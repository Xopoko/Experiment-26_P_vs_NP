## 16. IP = PSPACE and PCP (quoted)

These theorems do not prove $\mathrm{P}\neq\mathrm{NP}$, but are important as:
- flagship examples of **non-relativizing** methods (through arrhythmetization),
- source of central consequences (for example, hardness of approximation).

### 16.1. Interactive proofs: IP

**Definition.** A language $L$ belongs to $\mathrm{IP}$ if it exists
probabilistic polynomial verifier $V$ and interactive protocol
with proving $P$ (unbounded) such that:
- *(Completeness)* if $x\in L$, then there is a strategy $P$ under which $V$ accepts with probability $\ge 2/3$;
- *(Soundness)* if $x\notin L$, then for any strategy $P$ the verifier accepts with probability $\le 1/3$.

**Lemma 16.1 (easy side).** $\mathrm{IP}\subseteq\mathrm{PSPACE}$.

*Proof.* Consider the tree of all possible protocol transcripts
(the number of rounds and message lengths are polynomial).
The sheets are marked 0/1 (reject/accept).
At the verifier nodes we take the average of its random bits,
in the nodes of the prover - maximum according to the message.
The value of the root is equal to the optimal probability of acceptance.
This value is calculated by depth-first traversal, storing only the current transcript
and counters; memory $\mathrm{poly}(|x|)$ (time can be exponential).
$\square$

**Theorem (Shamir, 1992; cited).** $\mathrm{PSPACE}\subseteq\mathrm{IP}$, so $\mathrm{IP}=\mathrm{PSPACE}$.

### 16.2. Probabilistically Checkable Proofs: PCP

**Definition.** The class $\mathrm{PCP}(r(n),q(n))$ consists of languages for which
there is a probabilistic polynomial verifier that uses
$r(n)$ random bits and requests $q(n)$ "evidence" bits (oracle access),
with fullness/sonority as above.

**Lemma 16.2 (easy side).** $\mathrm{PCP}(O(\log_2 n), O(1))\subseteq\mathrm{NP}$.

*Proof.* Let $L\in\mathrm{PCP}(r(n),q(n))$ for $r(n)=O(\log_2 n)$
and $q(n)=O(1)$. The NP verifier guesses the proof string $\pi$
(polynomial length) and iterates over all $2^{r(|x|)}=\mathrm{poly}(|x|)$
random strings, simulating a verifier $V$ with oracle access to $\pi$.
We accept if the acceptance rate is $\ge 2/3$. $\square$

**Theorem (PCP, Arora-Safra; ALMSS; Dinur; cited).**
\mathrm{NP}\subseteq\mathrm{PCP}(O(\log_2 n), O(1)), so \mathrm{NP}=\mathrm{PCP}(O(\log_2 n), O(1)).

**Typical consequence (template formulation).** There is a constant
$\varepsilon>0$, such that the task is to distinguish feasible 3CNFs
from formulas for which it is impossible to satisfy more than $(1-\varepsilon)$ fraction of clauses,
NP-hard.

### 16.3-16.36. Research steps (outlined)

[Open file](research/16_complexity.md)
