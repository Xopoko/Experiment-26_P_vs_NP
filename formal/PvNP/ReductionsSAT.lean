import PvNP.SAT
import PvNP.Graph

namespace PvNP

def litPos (v : Nat) : Literal := { var := v, neg := false }
def litNeg (v : Nat) : Literal := { var := v, neg := true }

def maxVarClause (c : Clause) : Nat :=
  c.foldl (fun m l => Nat.max m l.var) 0

def maxVarCNF (f : CNF) : Nat :=
  f.foldl (fun m c => Nat.max m (maxVarClause c)) 0

def build3Clauses (l1 l2 : Literal) (ls : List Literal) (nextVar : Nat) : (CNF × Nat) :=
  match ls with
  | [] => ([[l1, l2, l2]], nextVar)
  | l3 :: [] => ([[l1, l2, l3]], nextVar)
  | l3 :: l4 :: rest =>
      let y := nextVar
      let first := [l1, l2, litPos y]
      let (tail, nextVar') := build3Clauses (litNeg y) l3 (l4 :: rest) (nextVar + 1)
      (first :: tail, nextVar')

def clauseTo3Sat (c : Clause) (nextVar : Nat) : (CNF × Nat) :=
  match c with
  | [] =>
      let y := nextVar
      let c1 := [litPos y, litPos y, litPos y]
      let c2 := [litNeg y, litNeg y, litNeg y]
      ([c1, c2], nextVar + 1)
  | [l] => ([[l, l, l]], nextVar)
  | [l1, l2] => ([[l1, l2, l2]], nextVar)
  | l1 :: l2 :: ls => build3Clauses l1 l2 ls nextVar

def cnfTo3SatAux (f : CNF) (nextVar : Nat) : (CNF × Nat) :=
  match f with
  | [] => ([], nextVar)
  | c :: rest =>
      let (c3, nextVar') := clauseTo3Sat c nextVar
      let (rest3, nextVar'') := cnfTo3SatAux rest nextVar'
      (c3 ++ rest3, nextVar'')

def satTo3Sat (f : CNF) : CNF :=
  let start := maxVarCNF f + 1
  (cnfTo3SatAux f start).1

def complementary (l1 l2 : Literal) : Bool :=
  (l1.var == l2.var) && (l1.neg != l2.neg)

def litAt (f : CNF) (i j : Nat) : Option Literal :=
  match f.get? i with
  | none => none
  | some c => c.get? j

def clauseIndex (u : Nat) : Nat := u / 3
def litIndex (u : Nat) : Nat := u % 3

def cliqueAdj (f : CNF) (u v : Nat) : Bool :=
  if clauseIndex u = clauseIndex v then
    false
  else
    match litAt f (clauseIndex u) (litIndex u), litAt f (clauseIndex v) (litIndex v) with
    | some l1, some l2 => !(complementary l1 l2)
    | _, _ => false

def cliqueGraph (f : CNF) : Graph :=
  { adj := cliqueAdj f }

structure CliqueInstance where
  G : Graph
  k : Nat

def threeSatToClique (f : CNF) : CliqueInstance :=
  { G := cliqueGraph f, k := f.length }

end PvNP
