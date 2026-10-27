## What changed

Proved `AlgebraicGeometry.Etale.properSupportExchange_range` by constructing the
adjunct of `properSupportPullbackSectionMap`, applying the existing geometric-fibre
restriction compatibility, and detecting the resulting isomorphism on geometric
stalks. The unit formula for ordinary exchange identifies the composite with the
literal proper-support inclusion. Private proved helpers establish monicity of
the inclusion and the pullback-projection calculation. The public statement,
universes, definitions and public imports are unchanged. Three redundant private
proof imports were removed. The node now records
this actual dependency route. The completed module compiled through `lcompile.py`
in 5.8 seconds with no errors or warnings.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.properSupportExchange_range`.
Holes added: zero. Holes left in delivered modules: zero.
The proof uses existing stated dependencies, including
`AlgebraicGeometry.Etale.properSupportPullbackSectionMap`, whose proof is still
an existing project obligation; it is not restated or proved here.

## No longer needed

No module is withdrawn. The direct proof dependencies
`lem-cbc-proper-support-geometric-stalk`,
`lem-weil-pbc-inverse-image-stalk-germ`, and
`prop-weil-pbc-inverse-image-modules-exact` are unnecessary here: their relevant
compatibilities are already included in
`lem-cbc-proper-support-fibre-restriction-compatibility`. They remain dependencies
of the lower-level theory. Removed direct imports:
`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk`,
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`, and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`; their necessary
public interfaces already come through the compatibility module.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. Stacks Tags 0F55 and 0F76 give the
stalk argument used here. The existing compatibility theorem already packages
the stalk comparison strongly enough to deduce invertibility, so the original
DAG's separate direct citations to the geometric-stalk and inverse-image exactness
theorems are redundant. The unit's route is preserved; no new statements or nodes
are introduced.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
