import Paperproof
import Std

namespace PvNP

structure Graph where
  adj : Nat -> Nat -> Bool

def Symmetric (G : Graph) : Prop :=
  ∀ u v, G.adj u v = G.adj v u

def LoopFree (G : Graph) : Prop :=
  ∀ u, G.adj u u = false

abbrev Clique (G : Graph) (k : Nat) (S : List Nat) : Prop :=
  S.length = k ∧
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = true)

end PvNP
