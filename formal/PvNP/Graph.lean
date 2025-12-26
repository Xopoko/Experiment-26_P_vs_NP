import Std

namespace PvNP

structure Graph where
  adj : Nat -> Nat -> Bool
  symm : ∀ u v, adj u v = adj v u
  loop_free : ∀ u, adj u u = false

abbrev Clique (G : Graph) (k : Nat) (S : List Nat) : Prop :=
  S.length = k ∧
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = true)

end PvNP
