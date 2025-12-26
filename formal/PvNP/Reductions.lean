import Paperproof
import PvNP.Defs

namespace PvNP

structure PolyTimeFunc where
  func : List Bool -> List Bool
  runtime : List Bool -> Nat
  poly_time : ∃ t, IsPoly t ∧ RunsIn runtime t

def manyOneReduction (A B : Language) : Prop :=
  ∃ f : PolyTimeFunc, ∀ x, x ∈ A ↔ f.func x ∈ B

def NPComplete (L : Language) : Prop :=
  InNP L ∧ ∀ A : Language, InNP A → manyOneReduction A L

end PvNP
