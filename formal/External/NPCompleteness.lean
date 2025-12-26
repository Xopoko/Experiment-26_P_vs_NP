import Paperproof
import PvNP.SAT
import PvNP.Graph
import PvNP.ReductionsSAT

namespace PvNP.External

-- ASSUMPTION: Srba (2010) "CNF-SAT ≤P 3SAT", Theorem on slide 3/13 (p.3).
-- SAT is equisatisfiable with its 3CNF transform.
axiom sat_to_3sat_correct : ∀ f : CNF, SatCNF f ↔ SatCNF (satTo3Sat f)

-- ASSUMPTION: Karp (1972), "Reducibility Among Combinatorial Problems",
-- p.9, statement "3SAT ≤P Clique".
axiom three_sat_to_clique_correct : ∀ f : CNF, Is3CNF f →
  (SatCNF f ↔ ∃ S, Clique (threeSatToClique f).G (threeSatToClique f).k S)

end PvNP.External
