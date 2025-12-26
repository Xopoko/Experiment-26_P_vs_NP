import Paperproof
import PvNP.Defs
import PvNP.Graph

namespace PvNP

-- Work-in-progress Lean proofs live here (real code, not doc-comments).

abbrev Vertex := Nat
abbrev Edge := Vertex × Vertex

def EmptySet : Set Vertex := fun _ => False
def FullSet : Set Vertex := fun _ => True

def boundary (G : Graph) (S : Set Vertex) : Set Edge :=
  fun e =>
    let (u, v) := e
    G.adj u v = true ∧ S u ∧ ¬ S v

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

-- TODO(Q39): replace `True` with the formal XOR-step obstruction statement.
theorem Q39_placeholder : True := by
  trivial

-- TODO(Q43.S136-logn-occurrence-scan): replace `True` with the formal flat local-EF(s) evaluation statement.
theorem Q43_placeholder : True := by
  trivial

end PvNP
