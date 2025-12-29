## 7. Three barriers: where "simple" ideas break down

These results do not prove $\mathrm{P}\neq\mathrm{NP}$, but are a filter:
they explain why many plausible ideas *cannot* solve the problem
in general terms.

Important: these barriers are formulated for circuit lower bounds/algorithmic techniques and do not provide direct restrictions for proof systems.
Within the AGENTS protocol, this file serves as a **Barrier certificate**: each barrier must be confirmed by an exact link (author/year/theorem/page).

### 7.1. Relativization (oracles)

**Definition (oracle MT).** Machine $M^A$ (with oracle $A\subseteq\Sigma^*$)
has an additional *oracle tape* and *oracle state*.
By writing the string $q$ to tape and entering this state, the machine in one step
gets the answer whether $q\in A$ is true.

The classes $\mathrm{P}^A,\mathrm{NP}^A$ are defined in the same way as $\mathrm{P},\mathrm{NP}$, but for machines with access to $A$.

**Theorem (Baker-Gill-Solovay, 1975; Katz lecture p.1, `../resources/downloads/jkatz_relativization_2005.pdf`).**
There are oracles $A,B$ such that $\mathrm{P}^A=\mathrm{NP}^A$ and
$\mathrm{P}^B\ne\mathrm{NP}^B$.

**Consequence (barrier).** If there was a proof that works the same
when adding an arbitrary oracle (i.e. *relativizes*), then it would give
same answer for all $A$. This is not possible due to the existence of $A,B$ above.

**An example of a relativizing technique.** "Naked" diagonalization and hierarchy theorems
in time/memory are usually transferred to the oracle world almost unchanged:
a language is constructed that diagonally "deceives" all the machines in the class,
even if they have access to $A$ (Arora-Impagliazzo-Vazirani 1992,
`../resources/downloads/arora_impagliazzo_vazirani_1992.pdf`).

**What does it mean to bypass.** What is needed is a non-relativizing argument: one that uses
calculation structure that disappears/breaks when adding an arbitrary oracle
(a typical example of ideas is arrhythmization and interactive protocols).


### 7.2. Natural proofs

The Razborov-Rudich barrier formalizes why "typical" lower bound methods on circuits do not extend to the general case.

A non-uniform circuit model is considered: $\mathrm{P/poly}$ are languages recognized by a family of polynomial-sized Boolean circuits.

**Definition (natural property, roughly).** Property $\mathcal{P}$ of Boolean functions
(according to their truth table) is called *natural* against the class of circuits
$\mathcal{C}$ if it satisfies three conditions:

1) *(Constructiveness)* according to the truth table of a function on $n$ bits
   one can check the membership of $\mathcal{P}$ in time $\mathrm{poly}(2^n)$;
2) *(Majority / largeness)* random Boolean function satisfies $\mathcal{P}$ with noticeable probability (usually $\ge 2^{-O(n)}$);
3) *(Utility / usefulness)* if the function satisfies $\mathcal{P}$,
   then it is not calculated by circuits from $\mathcal{C}$ (for example, of size $n^k$).

**Theorem (Razborov-Rudich, 1997, Thm. 4.1 p.3; `../resources/downloads/razborov_rudich_1997.pdf`).**
If there are pseudo-random functions (PRFs) of polynomial size circuits,
then there is no natural property useful against $\mathrm{P/poly}$.
Convention: the barrier relies on the existence of a PRF (standard cryptographic assumption); without PRF there is no restriction.


**Intuition.** Natural property that separates "random" functions from functions
from $\mathrm{P/poly}$, can be turned into a PRF distinguisher from true randomness -
which contradicts pseudorandomness.

**Example of "naturalness".** Many known lower bounds for limited classes
(AC0, monotonic schemes, etc.) define properties that
(a) are checked against the truth table and (b) are executed for a large fraction of the functions.
Barrier says such a pattern should not produce strong lower bounds
for general $\mathrm{P/poly}$ under standard cryptographic assumptions.

**What does it mean to bypass.** You need to violate at least one of the conditions: build
"unnatural" property (small set of functions), or refuse
constructiveness, or use assumptions/structure that do not lead
to PRF discrimination.

### 7.3. Algebrization

Aaronson-Wigderson (2008/2009) proposed increased relativization (Thm. 5.3 p.23; `../resources/downloads/aaronson_wigderson_2008.pdf`).

**Idea.** In a number of non-relativizing evidence (for example, through *arrhythmetization*)
we replace the Boolean function with its polynomial extension over the field and work
with polynomials. Algebrization formalizes a class of methods that remain
correct even if the machines are given access not only to the Boolean oracle $A$,
but also to its "algebraic" (low-grade) extension.

**Result (barrier, informally).** There are algebrizing oracles in which
key splits and inclusions take opposite values (similar to BGS),
therefore, methods that *algebraize* are unable to solve a number of central issues
(in particular, those where "oracle" reasoning alone is not enough).

Note: the barrier relies on special oracle constructions (as in relativization).

**What does it mean to bypass.** You need techniques that are not saved during the transition
to the algebraic extension of the oracle; roughly speaking, even more is required
a "structural" argument rather than a simply non-relativizing one.

**Fresh example of a barrier.** Chen-Hu-Ren (2025, arXiv:2511.14038) enhance
algebraization barriers for circuit lower bounds via communication
complexity XOR-Missing-String (`../resources/downloads/chen_hu_ren_2025_algebrization_barriers.pdf`).
