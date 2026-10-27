## What changed

Proved `AlgebraicGeometry.globalSections_isSeparable_of_isSmoothProjectiveCurve`
in `Sheaf.AlgebraicGeometry.GlobalSectionsSeparable` by applying the existing
`proper_geometricallyReduced_globalSections_isSeparable k X hA`.
Typeclass inference supplies properness via `IsHProjective.isProper` and geometric
reducedness via `Smooth.geometricallyReduced`, using the projectivity and smoothness
fields of `IsSmoothProjectiveCurve`. The statement, universes, canonical algebra
and the field structure `hA.toField` are unchanged. This realizes both steps of
`lem-pc-global-sections-separable` without changing the unit route.

Searches: LeanFinder returned general field separability results but no shorter
scheme theorem; Loogle did not recognize the project's `Algebra.IsSeparableExtension`;
launcher grep found no Mathlib match. Direct searches of both library roots found
the stated proper/geometrically reduced theorem, already proved. Read its signature
and proof, the smooth geometric reducedness instance, the projective properness
instance, and Stacks `varieties.tex`, Lemma 0BUG, clause (4).

Validation: the edited item compiled successfully through `lcompile.py` (7.1 seconds).
A second compile with `#print axioms` reported exactly `propext`, `Classical.choice`,
and `Quot.sound` (1.8 seconds). The diagnostic command was removed before delivery.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.globalSections_isSeparable_of_isSmoothProjectiveCurve`
(node `lem-pc-global-sections-separable`). No holes remain in the item, no holes
are added, and no statements are split off.

## No longer needed

Removed the redundant private import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: the public
`WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective` import already provides
it through `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
This removes a redundant direct import, not the projective properness dependency.
All five declared proof dependencies remain used, including the two definition
nodes through the statement and application. No DAG nodes or modules are withdrawn.
The geometric reducedness proof import and both existing public imports remain.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is valid. Its `lem-pc-projective-proper` Lean attachment names the
properness instance for projective space, rather than the general theorem for
projective morphisms. The current library supplies the general conclusion as
`AlgebraicGeometry.IsHProjective.isProper` in
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`; its proof uses precisely
properness of projective space and of closed immersions. No statement repair is needed.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
