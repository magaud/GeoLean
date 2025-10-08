# GeoLean

A hand-made translation of the GeoCoq library into Lean.

# technical details
GeoLean.lean somehow plays the role of the _CoqProject file.

* Name changes :

nat -> Nat (native type in Lean)

Sum -> SumGeoLean (already exists)

Prod -> ProdGeoLea (already exists)

* Undefined yet

TangentCC, Tangent, TangentAt in Definitions.lean

first_order_dedekind + section "Completeness" in continuity_axioms.lean
