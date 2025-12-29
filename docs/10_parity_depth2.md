## 10. Full lower estimate in depth 2: PARITY

Let us define $\mathrm{PARITY}_n(x_1,\dots,x_n)=x_1\oplus\cdots\oplus x_n$.
The value is 1 if and only if the number of ones is odd.

**Definition (term).** Term $T$ is a conjunction of literals in which each
the variable occurs no more than once: $T=\bigwedge_{i\in S} \ell_i$,
where $\ell_i\in\{x_i,\neg x_i\}$.
The set of inputs satisfying $T$ is the subcube obtained by committing
variables from $S$.

**Lemma 10.1.** If the term $T$ does not fix at least one variable
(that is, $S\ne\{1,\dots,n\}$), then on the set of inputs satisfying $T$,
the function $\mathrm{PARITY}_n$ is not a constant.

*Proof.* Let $j\notin S$ be a free variable.
Take any input $a$ satisfying $T$ and the input $a'$ obtained from $a$
inversion of only $x_j$. Then $a'$ also satisfies $T$,
but $\mathrm{PARITY}_n(a')=1-\mathrm{PARITY}_n(a)$ (exactly one bit changes).
This means that on $T^{-1}(1)$ the parity values are not constant. $\square$

**Lemma 10.2.** For $n\ge 1$, the set $\mathrm{PARITY}_n^{-1}(1)$ has size $2^{n-1}$.

*Proof.* Mapping $\phi(x_1,\dots,x_n)=(1-x_1,x_2,\dots,x_n)$ --
a bijection on $\{0,1\}^n$, which changes the parity (flips exactly one bit).
This means it matches inputs with parity 0 and 1 one-to-one;
and the total inputs are $2^n$, therefore, of each type exactly $2^{n-1}$. $\square$

**Theorem 10.3.** Any DNF formula that evaluates $\mathrm{PARITY}_n$ contains
at least $2^{n-1}$ terms. Similarly, any CNF formula for
$\mathrm{PARITY}_n$ contains at least $2^{n-1}$ clauses.

*Proof (DNF).* Let $F=\bigvee_{r=1}^m T_r$ be a DNF computing
$\mathrm{PARITY}_n$. For any $r$ the set $T_r^{-1}(1)$ must lie inside
$\mathrm{PARITY}_n^{-1}(1)$, otherwise there would be an input where $T_r=1$ but parity 0,
and then $F$ is wrong.

By Lemma 10.1, this is only possible if each $T_r$ fixes all variables,
that is, $T_r^{-1}(1)$ consists of exactly one input (minterm).

This means that each term covers at most one input from $\mathrm{PARITY}_n^{-1}(1)$.
By Lemma 10.2 there are $2^{n-1}$ such inputs, hence $m\ge 2^{n-1}$.

*Proof (CNF).* If $G$ is a CNF for $\mathrm{PARITY}_n$, then $\neg G$ is
DNF for $\neg\mathrm{PARITY}_n$ (pushing negations and applying de Morgan).
Since $\neg\mathrm{PARITY}_n$ also has exactly $2^{n-1}$ units, we use
DNF part to $\neg\mathrm{PARITY}_n$ and we get that $\neg G$ has $\ge 2^{n-1}$
terms, which means $G$ has $\ge 2^{n-1}$ clauses.

$\square$
