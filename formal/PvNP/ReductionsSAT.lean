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
  (cnfTo3SatAux f (maxVarCNF f + 1)).1

theorem is3clause_list (l1 l2 l3 : Literal) : Is3Clause [l1, l2, l3] := by
  simp [Is3Clause]

theorem is3cnf_nil : Is3CNF ([] : CNF) := by
  intro c hc
  cases hc

theorem is3cnf_single (c : Clause) (hc : Is3Clause c) : Is3CNF [c] := by
  intro c' hc'
  rcases List.mem_singleton.mp hc' with rfl
  exact hc

theorem is3cnf_cons (c : Clause) (f : CNF) (hc : Is3Clause c) (hf : Is3CNF f) : Is3CNF (c :: f) := by
  intro c' hc'
  rcases (List.mem_cons).1 hc' with h | h
  · simpa [h] using hc
  · exact hf _ h

theorem is3cnf_append (f g : CNF) (hf : Is3CNF f) (hg : Is3CNF g) : Is3CNF (f ++ g) := by
  intro c hc
  have h := List.mem_append.mp hc
  cases h with
  | inl h1 => exact hf _ h1
  | inr h2 => exact hg _ h2

theorem build3Clauses_is3cnf (ls : List Literal) :
    ∀ l1 l2 nextVar, Is3CNF (build3Clauses l1 l2 ls nextVar).1 := by
  induction ls with
  | nil =>
      intro l1 l2 nextVar
      simp [build3Clauses, is3cnf_single, is3clause_list]
  | cons l3 rest ih =>
      intro l1 l2 nextVar
      cases rest with
      | nil =>
          simp [build3Clauses, is3cnf_single, is3clause_list]
      | cons l4 rest2 =>
          have tail_is3 :
              Is3CNF (build3Clauses (litNeg nextVar) l3 (l4 :: rest2) (nextVar + 1)).1 :=
            ih (litNeg nextVar) l3 (nextVar + 1)
          have hfirst : Is3Clause [l1, l2, litPos nextVar] := by
            simp [Is3Clause]
          simpa [build3Clauses] using
            (is3cnf_cons ([l1, l2, litPos nextVar])
              (build3Clauses (litNeg nextVar) l3 (l4 :: rest2) (nextVar + 1)).1
              hfirst tail_is3)

theorem clauseTo3Sat_is3cnf (c : Clause) (nextVar : Nat) :
    Is3CNF (clauseTo3Sat c nextVar).1 := by
  cases c with
  | nil =>
      have h1 : Is3Clause [litPos nextVar, litPos nextVar, litPos nextVar] := by
        simp [Is3Clause]
      have h2 : Is3Clause [litNeg nextVar, litNeg nextVar, litNeg nextVar] := by
        simp [Is3Clause]
      exact is3cnf_cons _ _ h1 (is3cnf_single _ h2)
  | cons l1 rest =>
      cases rest with
      | nil =>
          have h : Is3Clause [l1, l1, l1] := by
            simp [Is3Clause]
          exact is3cnf_single _ h
      | cons l2 rest2 =>
          cases rest2 with
          | nil =>
              have h : Is3Clause [l1, l2, l2] := by
                simp [Is3Clause]
              exact is3cnf_single _ h
          | cons l3 rest3 =>
              exact build3Clauses_is3cnf (l3 :: rest3) l1 l2 nextVar

theorem cnfTo3SatAux_is3cnf (f : CNF) :
    ∀ nextVar, Is3CNF (cnfTo3SatAux f nextVar).1 := by
  induction f with
  | nil =>
      intro nextVar
      simp [cnfTo3SatAux, is3cnf_nil]
  | cons c rest ih =>
      intro nextVar
      have h1 : Is3CNF (clauseTo3Sat c nextVar).1 :=
        clauseTo3Sat_is3cnf c nextVar
      have h2 : Is3CNF (cnfTo3SatAux rest (clauseTo3Sat c nextVar).2).1 :=
        ih (clauseTo3Sat c nextVar).2
      simpa [cnfTo3SatAux] using is3cnf_append _ _ h1 h2

theorem satTo3Sat_is3cnf (f : CNF) : Is3CNF (satTo3Sat f) := by
  unfold satTo3Sat
  exact cnfTo3SatAux_is3cnf f (maxVarCNF f + 1)

def complementary (l1 l2 : Literal) : Bool :=
  (l1.var == l2.var) && (l1.neg != l2.neg)

def listGet? (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, Nat.succ n => listGet? rest n

def litAt (f : CNF) (i j : Nat) : Option Literal :=
  match listGet? f i with
  | none => none
  | some c => listGet? c j

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
