## 2. Equivalent "certificate" NP formulation

It is often convenient to define $\mathrm{NP}$ in terms of polynomially verifiable certificates.

**Definition (verifier).** A deterministic machine $V$ is a *verifier* for a language $L$ if there exists a polynomial $p$ such that

$$x\in L \iff \exists y\in\Sigma^\*,\ |y|\le p(|x|):\ V(x,y)=1,$$

and the running time of $V$ on the pair $(x,y)$ is limited by a polynomial in $|x|$.

**Lemma 2.1.** A language $L\in\mathrm{NP}$ if and only if it has a polynomial verifier.

*Proof.*

($\Rightarrow$) Let $L$ be recognized by $N$ in time $n^k$.
Certificate $y$ is a sequence of nondeterministic choices encoding a branch of length $\le n^k$.
The verifier $V(x,y)$ deterministically simulates $N$ over these choices and verifies that the branch accepts.
The length of $y$ and the simulation time are limited by a polynomial in $n$.

($\Leftarrow$) Let there be a verifier $V$ and a polynomial $p$.
$N$ on input $x$ nondeterministically guesses $y$ of length $\le p(|x|)$ and runs $V(x,y)$.
The accepting branch exists if and only if the certificate exists; time is polynomial.

$\square$
