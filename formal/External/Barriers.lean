namespace PvNP.External

-- ASSUMPTION: Baker-Gill-Solovay (1975), "Relativizations of the P = ? NP Question".
-- Lecture notes: Katz (2005), "Lecture on Relativization", main result, p.1.
-- There exist oracles A, B with P^A = NP^A and P^B != NP^B.
axiom bgs_relativization : True

-- ASSUMPTION: Razborov-Rudich (1997), "Natural Proofs", Theorem 4.1, p.3.
-- Under existence of PRFs, there is no natural property useful against P/poly.
axiom razborov_rudich_natural_proofs : True

-- ASSUMPTION: Aaronson-Wigderson (2008), "Algebrization: A New Barrier",
-- Theorem 5.3, p.23 (algebraic oracle separation between P and NP).
-- There exist algebrizing oracles separating P and NP.
axiom aaronson_wigderson_algebrization : True

end PvNP.External
