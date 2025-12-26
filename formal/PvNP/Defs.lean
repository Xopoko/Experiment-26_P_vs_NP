import Std

namespace PvNP

abbrev Language := Set (List Bool)

def IsPoly (t : Nat -> Nat) : Prop :=
  ∃ k, ∀ n, t n <= n ^ k + 1

def RunsIn (runtime : List Bool -> Nat) (t : Nat -> Nat) : Prop :=
  ∀ x, runtime x <= t x.length

def RunsIn2 (runtime : List Bool -> List Bool -> Nat) (t : Nat -> Nat) : Prop :=
  ∀ x w, runtime x w <= t (x.length + w.length)

structure Decider where
  decide : List Bool -> Bool
  runtime : List Bool -> Nat
  poly_time : ∃ t, IsPoly t ∧ RunsIn runtime t

def Decides (M : Decider) (L : Language) : Prop :=
  ∀ x, (M.decide x = true) ↔ x ∈ L

def InP (L : Language) : Prop :=
  ∃ M : Decider, Decides M L

structure Verifier where
  verify : List Bool -> List Bool -> Bool
  runtime : List Bool -> List Bool -> Nat
  poly_time : ∃ t, IsPoly t ∧ RunsIn2 runtime t
  witness_bound : ∃ k, ∀ x w, verify x w = true -> w.length <= x.length ^ k + 1

def InNP (L : Language) : Prop :=
  ∃ V : Verifier, ∀ x, x ∈ L ↔ ∃ w, V.verify x w = true

def P : Set Language := fun L => InP L

def NP : Set Language := fun L => InNP L

end PvNP
