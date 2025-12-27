import Paperproof
import PvNP.Core.Defs
import PvNP.Core.Graph

namespace PvNP

-- Work-in-progress Lean proofs live here (real code, not doc-comments).

abbrev Vertex := Nat
abbrev Edge := Vertex × Vertex

def edgeSwap (e : Edge) : Edge := (e.2, e.1)

theorem edgeSwap_involutive (e : Edge) : edgeSwap (edgeSwap e) = e := by
  cases e with
  | mk u v =>
    rfl

def EmptySet : Set Vertex := fun _ => False
def FullSet : Set Vertex := fun _ => True

def boundary (G : Graph) (S : Set Vertex) : Set Edge :=
  fun e =>
    let (u, v) := e
    G.adj u v = true ∧ S u ∧ ¬ S v

def frontier (G : Graph) (S : Set Vertex) : Set Edge :=
  fun e => boundary G S e ∨ boundary G S (edgeSwap e)

theorem boundary_empty (G : Graph) : ∀ e, ¬ boundary G EmptySet e := by
  intro e
  cases e with
  | mk u v =>
    simp [boundary, EmptySet]

theorem boundary_full (G : Graph) : ∀ e, ¬ boundary G FullSet e := by
  intro e
  cases e with
  | mk u v =>
    simp [boundary, FullSet]

-- Q39.S21-boundary-complement-duality: complement flips boundary orientation in symmetric graphs.
theorem Q39_boundary_compl_swap (G : Graph) (hG : Symmetric G) (S : Set Vertex) :
    ∀ e, boundary G (fun x => ¬ S x) e ↔ boundary G S (edgeSwap e) := by
  intro e
  cases e with
  | mk u v =>
    constructor
    · intro h
      have h' : G.adj u v = true ∧ ¬ S u ∧ S v := by
        simpa [boundary] using h
      have h1 : G.adj v u = true := by
        calc
          G.adj v u = G.adj u v := by
            symm
            exact hG u v
          _ = true := h'.1
      -- Expand boundary on the swapped edge.
      simp [boundary]
      exact And.intro h1 (And.intro h'.2.2 h'.2.1)
    · intro h
      have h' : G.adj v u = true ∧ S v ∧ ¬ S u := by
        simpa [boundary] using h
      have h1 : G.adj u v = true := by
        calc
          G.adj u v = G.adj v u := by
            exact hG u v
          _ = true := h'.1
      -- Expand boundary on the original edge.
      simp [boundary]
      exact And.intro h1 (And.intro h'.2.2 h'.2.1)

-- Q39.S22-2k-two-strip-frontier-obstruction: undirected frontier is complement-invariant.
theorem Q39_frontier_compl (G : Graph) (hG : Symmetric G) (S : Set Vertex) :
    ∀ e, frontier G S e ↔ frontier G (fun x => ¬ S x) e := by
  intro e
  have hswap : boundary G (fun x => ¬ S x) e ↔ boundary G S (edgeSwap e) :=
    Q39_boundary_compl_swap G hG S e
  have hswap' : boundary G (fun x => ¬ S x) (edgeSwap e) ↔ boundary G S e := by
    have h := Q39_boundary_compl_swap G hG S (edgeSwap e)
    simpa [edgeSwap_involutive] using h
  constructor
  · intro h
    cases h with
    | inl hleft =>
        exact Or.inr (hswap'.mpr hleft)
    | inr hright =>
        exact Or.inl (hswap.mpr hright)
  · intro h
    cases h with
    | inl hleft =>
        exact Or.inr (hswap.mp hleft)
    | inr hright =>
        exact Or.inl (hswap'.mp hright)

-- Q39.S24-2k-two-strip-interval-obstruction: frontier is invariant under edge orientation.
theorem Q39_frontier_swap (G : Graph) (S : Set Vertex) (e : Edge) :
    frontier G S (edgeSwap e) ↔ frontier G S e := by
  constructor <;> intro h
  · have h' : boundary G S (edgeSwap e) ∨ boundary G S e := by
      simpa [frontier, edgeSwap_involutive] using h
    cases h' with
    | inl hswap =>
        have : boundary G S e ∨ boundary G S (edgeSwap e) := Or.inr hswap
        simpa [frontier] using this
    | inr hmain =>
        have : boundary G S e ∨ boundary G S (edgeSwap e) := Or.inl hmain
        simpa [frontier] using this
  · have h' : boundary G S e ∨ boundary G S (edgeSwap e) := by
      simpa [frontier] using h
    cases h' with
    | inl hmain =>
        have : boundary G S (edgeSwap e) ∨ boundary G S e := Or.inr hmain
        simpa [frontier, edgeSwap_involutive] using this
    | inr hswap =>
        have : boundary G S (edgeSwap e) ∨ boundary G S e := Or.inl hswap
        simpa [frontier, edgeSwap_involutive] using this

-- Q39.S25-2k-two-strip-interval-rank-check: frontier edges cross the cut.
theorem Q39_frontier_cross (G : Graph) (S : Set Vertex) (e : Edge) :
    frontier G S e → (S e.1 ∧ ¬ S e.2) ∨ (S e.2 ∧ ¬ S e.1) := by
  intro h
  cases e with
  | mk u v =>
    have h' : boundary G S (u, v) ∨ boundary G S (v, u) := by
      simpa [frontier, edgeSwap] using h
    cases h' with
    | inl h1 =>
        exact Or.inl h1.2
    | inr h2 =>
        exact Or.inr h2.2

-- Q39.S26-2k-two-strip-frontier-adj: frontier edges are real edges in symmetric graphs.
theorem Q39_frontier_adj (G : Graph) (hG : Symmetric G) (S : Set Vertex) (e : Edge) :
    frontier G S e → G.adj e.1 e.2 = true := by
  intro h
  cases e with
  | mk u v =>
    have h' : boundary G S (u, v) ∨ boundary G S (v, u) := by
      simpa [frontier, edgeSwap] using h
    cases h' with
    | inl h1 =>
        exact h1.1
    | inr h2 =>
        have huv : G.adj v u = true := h2.1
        calc
          G.adj u v = G.adj v u := by
            exact hG u v
          _ = true := huv

-- Q43.S139-polym-avoids-thm41-branch: IsPoly is monotone under pointwise upper bounds.
theorem Q43_IsPoly_of_le {t s : Nat -> Nat} (hpoly : IsPoly t) (hle : ∀ n, s n <= t n) :
    IsPoly s := by
  rcases hpoly with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  exact le_trans (hle n) (hk n)

-- Q43.S140-polym-below-threshold: explicit polynomial bounds imply IsPoly.
theorem Q43_IsPoly_of_le_pow {s : Nat -> Nat} (k : Nat) (hle : ∀ n, s n <= n ^ k) :
    IsPoly s := by
  refine ⟨k, ?_⟩
  intro n
  exact le_trans (hle n) (Nat.le_succ _)

-- Q43.S170-explicit-c1c2-thm41: package explicit constants for Thm. 4.1.
def Q43_thm41_c2 (A : Nat) : Nat := 8 * A * 152

def Q43_thm41_c1 (A : Nat) : Nat := 16 * 152 * Q43_thm41_c2 A

-- Q43.S171-check-thm41-threshold: exp base 2 for HR'22 conventions.
def Q43_exp2 (x : Nat) : Nat := 2 ^ x

-- Q43.S172-exp2-consistency: generic exp base for clarity.
def Q43_exp_base (b x : Nat) : Nat := b ^ x

theorem Q43_exp2_eq_base (x : Nat) : Q43_exp2 x = Q43_exp_base 2 x := by
  rfl

-- Q43.S173-exp2-c1c2-rescale: constants already in base-2 conventions.
def Q43_thm41_c2_exp2 (A : Nat) : Nat := Q43_thm41_c2 A

def Q43_thm41_c1_exp2 (A : Nat) : Nat := Q43_thm41_c1 A

theorem Q43_thm41_c1_exp2_eq (A : Nat) : Q43_thm41_c1_exp2 A = Q43_thm41_c1 A := by
  rfl

theorem Q43_thm41_c2_exp2_eq (A : Nat) : Q43_thm41_c2_exp2 A = Q43_thm41_c2 A := by
  rfl

-- TODO(Q43.S137-logn-remaining-scan): replace `True` with the formal flat local-EF(s) evaluation statement.
theorem Q43_placeholder : True := by
  trivial

end PvNP
