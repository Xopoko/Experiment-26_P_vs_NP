import PvNP.SAT
import PvNP.Graph
import PvNP.ReductionsSAT

namespace PvNP.External

-- ASSUMPTION: Sipser, "Introduction to the Theory of Computation", NP-completeness chapter.
-- SAT is equisatisfiable with its 3CNF transform (and the transform is 3CNF).
axiom sat_to_3sat_correct : ∀ f : CNF, SatCNF f ↔ SatCNF (satTo3Sat f)
axiom sat_to_3sat_is3cnf : ∀ f : CNF, Is3CNF (satTo3Sat f)

-- ASSUMPTION: Karp (1972) / Sipser, reduction 3SAT -> CLIQUE.
axiom three_sat_to_clique_correct : ∀ f : CNF, Is3CNF f →
  (SatCNF f ↔ ∃ S, Clique (threeSatToClique f).G (threeSatToClique f).k S)

end PvNP.External
