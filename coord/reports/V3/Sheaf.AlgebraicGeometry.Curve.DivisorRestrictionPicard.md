## What changed

Completed `AlgebraicGeometry.Scheme.Hom.exists_divisor_restriction_picard` in
`Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard`, preserving its statement and imports.
The proof follows the existing DAG plan: use continuity and injectivity of the open immersion
for closed preimages, then induct on the finitely supported divisor. Zero restricts to zero;
restrictions add because preimages are unique; a point divisor restricts to its closed
preimage or zero. `pic_restriction_point_lift` and `pic_restriction_boundary_trivial` give the
Picard equality in the two single-point cases, and homomorphism laws handle coefficients.

The local compile through `lcompile.py` passed without warnings. Searches in the source
library and Mathlib found no arbitrary-divisor restriction theorem; Loogle confirmed
`Finsupp.induction_linear`, which is used. LeanFinder returned unrelated elliptic-curve,
Proj and rational-map results, and the Mathlib grep returned meromorphic divisor restriction
and ring Picard-group results rather than this scheme-level statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.exists_divisor_restriction_picard`
(node `lem-sc-divisor-restriction-picard`). No holes added, split off, or left in the item.
Both existing proof dependencies are used; this delivery does not modify their modules.
The zero divisor and zero coefficient cases are included in the induction. The proof also
covers an empty boundary, when every single-point divisor takes the retained-point branch.

## No longer needed

None. Both existing proof-only imports are used:
`Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` and
`Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial`.
Their nodes `lem-sc-pic-restriction-point-lift` and
`lem-sc-pic-restriction-boundary-trivial` remain needed. No route is changed and no new
nodes or modules are delivered.

## Where the brief, the DAG or earlier work was wrong

None. The existing numbered argument can be implemented directly using the two stated
geometric comparisons and finite-support induction. The unit route is preserved.

## Second reading by V3

1. I compared the delivered declaration with the repository version; its signature is unchanged. Verdict: pass.
2. `lcompile.py` compiles the module cleanly; no forbidden declarations or unsplit `sorry` remain. Verdict: pass.
3. No statements were split off or added. The proof covers zero divisors, zero coefficients, and an empty boundary, and uses the existing single-point comparisons. Verdict: pass.
4. The unit route is preserved, both proof-only imports are used, and no shorter existing theorem was found. Verdict: pass.
5. The DAG node's statement, proof, dependencies, origin, and Lean declaration agree with the proof. Verdict: pass.

I changed only this report by adding the second-reading record; no Lean or DAG files changed.
