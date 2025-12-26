namespace PvNP.External

-- ASSUMPTION: Baker-Gill-Solovay (1975), "Relativizations of the P = ? NP Question".
-- There exist oracles A, B with P^A = NP^A and P^B != NP^B.
axiom bgs_relativization : True

-- ASSUMPTION: Razborov-Rudich (1997), "Natural Proofs".
-- Under existence of PRFs, there is no natural property useful against P/poly.
axiom razborov_rudich_natural_proofs : True

-- ASSUMPTION: Aaronson-Wigderson (2008), "Algebrization: A New Barrier".
-- There exist algebrizing oracles separating P and NP.
axiom aaronson_wigderson_algebrization : True

end PvNP.External
