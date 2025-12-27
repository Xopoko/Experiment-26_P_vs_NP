import Paperproof
import PvNP.Core.Defs

namespace PvNP

structure Literal where
  var : Nat
  neg : Bool

abbrev Clause := List Literal
abbrev CNF := List Clause

abbrev Assignment := Nat -> Bool

def evalLiteral (σ : Assignment) (l : Literal) : Bool :=
  if l.neg then Bool.not (σ l.var) else σ l.var

def evalClause (σ : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral σ)

def evalCNF (σ : Assignment) (f : CNF) : Bool :=
  f.all (evalClause σ)

def SatCNF (f : CNF) : Prop :=
  ∃ σ, evalCNF σ f = true

def Is3Clause (c : Clause) : Prop := c.length = 3

def Is3CNF (f : CNF) : Prop :=
  ∀ c ∈ f, Is3Clause c

-- Syntax-level languages (no bitstring encoding yet).
def SATSyntax : Set CNF := fun f => SatCNF f

def ThreeSATSyntax : Set CNF := fun f => SatCNF f ∧ Is3CNF f

end PvNP
