## 1. Formal setting

Let $\Sigma$ be a finite alphabet, $\Sigma^\*$ the set of all finite strings over $\Sigma$.

**A language** is a set $L\subseteq\Sigma^\*$.

We fix the standard model: deterministic/non-deterministic multi-tape MT.
Time complexity is the number of steps as a function of input length $n=|x|$.

**Definition (class $\mathrm{P}$).** $L\in\mathrm{P}$ if there is a deterministic MT $M$ and a constant $k$.
For all $x\in\Sigma^\*$ machine $M$ stops in $O(|x|^k)$ steps and accepts if and only if $x\in L$.

**Definition (class $\mathrm{NP}$).** $L\in\mathrm{NP}$ if there is a nondeterministic MT $N$ and a constant $k$.
$N$ stops in $O(|x|^k)$ steps on all branches, and $x\in L$ if and only if a receiving branch $N(x)$ exists.

**Note (robustness).** The choice of model and encoding affects only the polynomial factors.
It is enough to estimate the reduction time by the length of the natural description (formula/graph).

**Conjecture $\mathrm{P}\neq\mathrm{NP}$.** There is a language $L\in\mathrm{NP}$ such that $L\notin\mathrm{P}$.

**Lean-skeleton:** definitions of the language/classes $P,NP$ are included in `formal/PvNP/Core/Defs.lean`.
