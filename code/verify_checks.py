"""Project sanity checks.

Run:
  scripts/verify_all.sh

This file contains the executable checks that used to live in code cells of the
legacy notebook format.
"""

# --- notebook cell 7 ---
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import random
from typing import Iterable


Literal = int  # +i means x_i, -i means ¬x_i, variables indexed from 1
Clause = tuple[Literal, ...]
CNF = list[Clause]


def eval_literal(lit: Literal, assignment: dict[int, bool]) -> bool:
    var = abs(lit)
    val = assignment[var]
    return val if lit > 0 else (not val)


def eval_cnf(formula: CNF, assignment: dict[int, bool]) -> bool:
    return all(any(eval_literal(l, assignment) for l in clause) for clause in formula)


def satisfiable(formula: CNF, num_vars: int) -> bool:
    for bits in product([False, True], repeat=num_vars):
        assignment = {i + 1: bits[i] for i in range(num_vars)}
        if eval_cnf(formula, assignment):
            return True
    return False


def to_3cnf(formula: CNF, num_vars: int) -> tuple[CNF, int]:
    next_var = num_vars + 1
    out: CNF = []

    for clause in formula:
        k = len(clause)
        if k == 0:
            # empty clause -> unsatisfiable; keep as is
            out.append(clause)
            continue
        if k == 1:
            l1 = clause[0]
            out.append((l1, l1, l1))
            continue
        if k == 2:
            l1, l2 = clause
            out.append((l1, l2, l2))
            continue
        if k == 3:
            out.append(tuple(clause))
            continue

        # k > 3
        l1, l2, *rest = clause
        y_vars = list(range(next_var, next_var + (k - 3)))
        next_var += (k - 3)

        # (l1 ∨ l2 ∨ y1)
        out.append((l1, l2, y_vars[0]))

        # (¬y_{i} ∨ l_{i+3} ∨ y_{i+1}) for i=0..k-5
        for i in range(k - 4):
            out.append((-y_vars[i], rest[i], y_vars[i + 1]))

        # last: (¬y_{k-4} ∨ l_{k-1} ∨ l_k)
        out.append((-y_vars[-1], rest[-2], rest[-1]))

    return out, next_var - 1


def random_cnf(num_vars: int, num_clauses: int, min_len: int = 1, max_len: int = 5) -> CNF:
    out: CNF = []
    for _ in range(num_clauses):
        k = random.randint(min_len, max_len)
        clause: list[int] = []
        for _ in range(k):
            v = random.randint(1, num_vars)
            clause.append(v if random.random() < 0.5 else -v)
        out.append(tuple(clause))
    return out


def check_sat_to_3sat_trials(trials: int = 200, seed: int = 0) -> None:
    random.seed(seed)
    for t in range(trials):
        n = random.randint(1, 6)
        m = random.randint(0, 8)
        f = random_cnf(n, m)
        f3, n3 = to_3cnf(f, n)
        a = satisfiable(f, n)
        b = satisfiable(f3, n3)
        if a != b:
            raise AssertionError((t, n, m, f, f3, n3, a, b))


check_sat_to_3sat_trials()
print("OK: SAT ↔ 3SAT на случайных малых тестах")


# --- notebook cell 9 ---
from itertools import combinations, product


def is_complementary(a: Literal, b: Literal) -> bool:
    return a == -b


def three_sat_to_clique(formula_3cnf: CNF) -> tuple[dict[tuple[int, int], set[tuple[int, int]]], int]:
    # vertices are (clause_index, literal)
    adj: dict[tuple[int, int], set[tuple[int, int]]] = {}
    m = len(formula_3cnf)

    vertices: list[tuple[int, int]] = []
    for i, clause in enumerate(formula_3cnf):
        if len(clause) != 3:
            raise ValueError("expected 3CNF")
        for lit in clause:
            v = (i, lit)
            vertices.append(v)
            adj[v] = set()

    for (i, lit1), (j, lit2) in combinations(vertices, 2):
        if i == j:
            continue
        if is_complementary(lit1, lit2):
            continue
        adj[(i, lit1)].add((j, lit2))
        adj[(j, lit2)].add((i, lit1))

    return adj, m


def has_clique_one_per_clause(adj: dict[tuple[int, int], set[tuple[int, int]]], formula_3cnf: CNF) -> bool:
    # brute force: choose 1 literal per clause
    choices = [list(clause) for clause in formula_3cnf]
    for picked_lits in product(*choices):
        vertices = [(i, picked_lits[i]) for i in range(len(picked_lits))]
        ok = True
        for u, v in combinations(vertices, 2):
            if v not in adj[u]:
                ok = False
                break
        if ok:
            return True
    return False


def random_3cnf(num_vars: int, num_clauses: int) -> CNF:
    out: CNF = []
    for _ in range(num_clauses):
        clause: list[int] = []
        for _ in range(3):
            v = random.randint(1, num_vars)
            clause.append(v if random.random() < 0.5 else -v)
        out.append(tuple(clause))
    return out


def check_3sat_to_clique_trials(trials: int = 200, seed: int = 0) -> None:
    random.seed(seed)
    for t in range(trials):
        n = random.randint(1, 6)
        m = random.randint(0, 7)
        f3 = random_3cnf(n, m)
        adj, k = three_sat_to_clique(f3)
        a = satisfiable(f3, n)
        b = has_clique_one_per_clause(adj, f3)
        if a != b:
            raise AssertionError((t, n, m, f3, a, b, k))


check_3sat_to_clique_trials()
print("OK: 3SAT ↔ CLIQUE на случайных малых тестах")


# --- notebook cell 11 ---
from itertools import combinations
import random


Edge = tuple[int, int]  # always (u, v) with u < v


def random_graph(n: int, p: float = 0.5) -> set[Edge]:
    edges: set[Edge] = set()
    for u, v in combinations(range(n), 2):
        if random.random() < p:
            edges.add((u, v))
    return edges


def complement_graph(n: int, edges: set[Edge]) -> set[Edge]:
    comp: set[Edge] = set()
    for u, v in combinations(range(n), 2):
        if (u, v) not in edges:
            comp.add((u, v))
    return comp


def is_clique(vertices: tuple[int, ...], edges: set[Edge]) -> bool:
    for u, v in combinations(vertices, 2):
        a, b = (u, v) if u < v else (v, u)
        if (a, b) not in edges:
            return False
    return True


def is_independent(vertices: tuple[int, ...], edges: set[Edge]) -> bool:
    for u, v in combinations(vertices, 2):
        a, b = (u, v) if u < v else (v, u)
        if (a, b) in edges:
            return False
    return True


def is_vertex_cover(vertices: tuple[int, ...], edges: set[Edge]) -> bool:
    cover = set(vertices)
    for u, v in edges:
        if u not in cover and v not in cover:
            return False
    return True


def max_clique_size(n: int, edges: set[Edge]) -> int:
    best = 0
    for r in range(n + 1):
        for vs in combinations(range(n), r):
            if is_clique(vs, edges):
                best = r
    return best


def max_independent_size(n: int, edges: set[Edge]) -> int:
    best = 0
    for r in range(n + 1):
        for vs in combinations(range(n), r):
            if is_independent(vs, edges):
                best = r
    return best


def min_vertex_cover_size(n: int, edges: set[Edge]) -> int:
    for r in range(n + 1):
        for vs in combinations(range(n), r):
            if is_vertex_cover(vs, edges):
                return r
    raise RuntimeError("unreachable")


def check_clique_is_vc_trials(trials: int = 100, seed: int = 0) -> None:
    random.seed(seed)
    for t in range(trials):
        n = random.randint(1, 9)
        p = random.random()
        g = random_graph(n, p=p)
        gc = complement_graph(n, g)

        omega = max_clique_size(n, g)
        alpha_comp = max_independent_size(n, gc)
        assert omega == alpha_comp

        alpha = max_independent_size(n, g)
        tau = min_vertex_cover_size(n, g)
        assert tau == n - alpha

        # decision versions
        k = random.randint(0, n)
        assert (omega >= k) == (alpha_comp >= k)
        assert (alpha >= k) == (tau <= n - k)


check_clique_is_vc_trials()
print("OK: CLIQUE ↔ IS ↔ VC на случайных малых графах")


# --- notebook cell 16 ---
from itertools import product


def parity(bits: tuple[int, ...]) -> int:
    return sum(bits) % 2


def check_parity_subcubes(nmax: int = 10) -> None:
    for n in range(1, nmax + 1):
        ones = sum(parity(bits) == 1 for bits in product([0, 1], repeat=n))
        assert ones == 2 ** (n - 1)

        # Verify Lemma 10.1 on all nontrivial subcubes represented by partial assignments.
        # partial[i] in {0, 1, None}, where None means "free".
        for partial in product([0, 1, None], repeat=n):
            if None not in partial:
                continue
            j = partial.index(None)
            base = [0 if v is None else v for v in partial]
            b1 = tuple(base)
            base[j] ^= 1
            b2 = tuple(base)
            assert parity(b1) != parity(b2)

        print(f"n={n}: OK (|PARITY^-1(1)|={ones}, all nontrivial subcubes bichromatic)")


check_parity_subcubes(10)


# --- notebook cell 20 ---

from functools import lru_cache
from collections import deque
from itertools import combinations
import math
import random


def savitch_reachable(n: int, edges: set[tuple[int, int]], s: int, t: int) -> bool:
    adj = {i: set() for i in range(n)}
    for u, v in edges:
        adj[u].add(v)

    # any reachable pair has a simple path of length ≤ n-1
    L = max(1, n - 1)
    k = math.ceil(math.log2(L))

    @lru_cache(maxsize=None)
    def reach(u: int, v: int, kk: int) -> bool:
        if kk == 0:
            return u == v or (v in adj[u])
        for m in range(n):
            if reach(u, m, kk - 1) and reach(m, v, kk - 1):
                return True
        return False

    return reach(s, t, k)


def bfs_reachable(n: int, edges: set[tuple[int, int]], s: int, t: int) -> bool:
    adj = {i: set() for i in range(n)}
    for u, v in edges:
        adj[u].add(v)

    q = deque([s])
    seen = {s}
    while q:
        u = q.popleft()
        if u == t:
            return True
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                q.append(v)
    return False


def random_digraph(n: int, p: float) -> set[tuple[int, int]]:
    edges: set[tuple[int, int]] = set()
    for u in range(n):
        for v in range(n):
            if u == v:
                continue
            if random.random() < p:
                edges.add((u, v))
    return edges


def check_savitch_trials(trials: int = 100, seed: int = 0) -> None:
    random.seed(seed)
    for _ in range(trials):
        n = random.randint(1, 9)
        p = random.random() * 0.6
        edges = random_digraph(n, p)
        s = random.randrange(n)
        t = random.randrange(n)
        a = savitch_reachable(n, edges, s, t)
        b = bfs_reachable(n, edges, s, t)
        assert a == b


check_savitch_trials()
print("OK: Savitch-REACH совпадает с BFS на малых случайных графах")


# --- notebook cell 23 ---
from itertools import combinations, permutations, product


def php_cnf(num_holes: int, num_pigeons: int) -> tuple[CNF, int]:
    if num_holes <= 0 or num_pigeons <= 0:
        raise ValueError("num_holes and num_pigeons must be positive")

    def var(i: int, j: int) -> int:
        return i * num_holes + j + 1

    cnf: CNF = []
    # Each pigeon is in at least one hole.
    for i in range(num_pigeons):
        cnf.append(tuple(var(i, j) for j in range(num_holes)))

    # No hole contains two pigeons.
    for j in range(num_holes):
        for i1, i2 in combinations(range(num_pigeons), 2):
            cnf.append((-var(i1, j), -var(i2, j)))

    return cnf, num_pigeons * num_holes


def _is_tautological_clause(clause: frozenset[int]) -> bool:
    return any(-lit in clause for lit in clause)


def resolution_refutable(cnf: CNF, *, max_clauses: int = 20_000) -> bool:
    clauses: set[frozenset[int]] = {frozenset(c) for c in cnf}
    clauses = {c for c in clauses if not _is_tautological_clause(c)}

    changed = True
    while changed:
        changed = False
        clause_list = list(clauses)
        for i in range(len(clause_list)):
            c1 = clause_list[i]
            for j in range(i + 1, len(clause_list)):
                c2 = clause_list[j]
                for lit in c1:
                    if -lit not in c2:
                        continue
                    resolvent = (c1 - {lit}) | (c2 - {-lit})
                    if _is_tautological_clause(resolvent):
                        continue
                    if not resolvent:
                        return True
                    if resolvent not in clauses:
                        clauses.add(resolvent)
                        changed = True
                        if len(clauses) > max_clauses:
                            return False

    return False


def check_php_small() -> None:
    for n in range(1, 4):
        cnf, num_vars = php_cnf(n, n + 1)
        assert satisfiable(cnf, num_vars) is False
    print("OK: PHP_{n+1}^n не выполнима для n=1..3 (полный перебор)")

    cnf, _ = php_cnf(2, 3)
    assert resolution_refutable(cnf)
    print("OK: для PHP_3^2 найдено резолюционное опровержение (наивное замыкание)")


check_php_small()


def php_var(num_holes: int, pigeon: int, hole: int) -> int:
    return pigeon * num_holes + hole + 1


def php_unvar(num_holes: int, v: int) -> tuple[int, int]:
    if v <= 0:
        raise ValueError("variable id must be positive")
    v -= 1
    return v // num_holes, v % num_holes


def positive_clause_php(clause: Clause, num_holes: int, num_pigeons: int) -> Clause:
    out: set[int] = set()
    for lit in clause:
        if lit > 0:
            out.add(lit)
            continue
        pigeon, hole = php_unvar(num_holes, -lit)
        for other in range(num_pigeons):
            if other != pigeon:
                out.add(php_var(num_holes, other, hole))
    return tuple(sorted(out))


def critical_assignments_php(num_holes: int, num_pigeons: int) -> list[dict[int, bool]]:
    if num_pigeons != num_holes + 1:
        raise ValueError("expected num_pigeons = num_holes + 1")

    all_vars = [php_var(num_holes, i, j) for i in range(num_pigeons) for j in range(num_holes)]
    holes = list(range(num_holes))
    out: list[dict[int, bool]] = []

    for left_out in range(num_pigeons):
        pigeons = [i for i in range(num_pigeons) if i != left_out]
        for perm in permutations(holes):
            assignment = {v: False for v in all_vars}
            for i, hole in zip(pigeons, perm):
                assignment[php_var(num_holes, i, hole)] = True
            out.append(assignment)

    return out


def check_positive_translation_lemma(max_n: int = 4) -> None:
    for n in range(1, max_n + 1):
        num_holes = n
        num_pigeons = n + 1
        cnf, _ = php_cnf(num_holes, num_pigeons)
        crit = critical_assignments_php(num_holes, num_pigeons)

        for clause in cnf:
            clause_plus = positive_clause_php(clause, num_holes, num_pigeons)
            for a in crit:
                lhs = any(eval_literal(lit, a) for lit in clause)
                rhs = any(a[v] for v in clause_plus)
                assert lhs == rhs

    print("OK: Lemma 15.4 verified on all initial PHP clauses for n=1..4")


check_positive_translation_lemma(4)


def php_inequalities_satisfiable(num_holes: int) -> bool:
    """Brute-force check for the natural inequality encoding of PHP.

    Variables: x_{i,j} in {0,1}, i in [0..n], j in [0..n-1].
    Constraints:
      - for each pigeon i: sum_j x_{i,j} >= 1
      - for each hole j:   sum_i x_{i,j} <= 1
    """
    if num_holes <= 0:
        raise ValueError("num_holes must be positive")

    num_pigeons = num_holes + 1
    num_vars = num_pigeons * num_holes

    for bits in product([0, 1], repeat=num_vars):
        def x(i: int, j: int) -> int:
            return bits[i * num_holes + j]

        if any(sum(x(i, j) for j in range(num_holes)) < 1 for i in range(num_pigeons)):
            continue
        if any(sum(x(i, j) for i in range(num_pigeons)) > 1 for j in range(num_holes)):
            continue
        return True

    return False


for n in range(1, 4):
    assert php_inequalities_satisfiable(n) is False
print("OK: inequality encoding of PHP is unsatisfiable for n=1..3 (brute force)")
