+++
id = "sk-p-trace-coeff"
kind = "section"
title = "Finite-level coefficient change"
order = 2382
uses = ["sk-d-setup", "sk-d-six", "sk-d-weil", "sk-thm-sf-ctf-stability"]
lean = ["AlgebraicGeometry.ProEtale.nonempty_iso_comp_lowerShriek_and_upperStar"]
+++
*Proposition (sketch).*

Compact cohomology and geometric stalks commute with finite-level
coefficient reduction, with their specified Frobenius
maps.

## Proof

For a homomorphism $A\to B$ of finite coefficient rings annihilated by
integers invertible in $k$, derived scalar extension $-\otimes_A^{\mathrm L}B$
preserves bounded constructibility and finite Tor amplitude by
[sk-thm-sf-ctf-stability], and commutes with the operations of
[sk-d-six] by the natural comparison maps. Applying this to
$Ra_{X!}$ and to a geometric stalk gives the two displayed compatibilities,
and the comparisons are natural, hence compatible with the Frobenius maps
of [sk-d-weil]. For an adic system the same statement holds levelwise,
the transition maps being the reductions of one another.

Uses: [sk-d-setup], [sk-d-six], [sk-d-weil], [sk-thm-sf-ctf-stability]
