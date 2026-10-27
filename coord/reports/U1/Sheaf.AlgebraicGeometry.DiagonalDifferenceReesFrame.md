## What changed

Proved `AlgebraicGeometry.DiagonalDifferenceReesFrame.diagonal_difference_rees_frame`
with its original signature. The proof assembles the signed normal frame, the centred
étale deformation chart, uniqueness under open restriction, and the matrix frame change.

The existing `NormalFrame`, `CentredChart` and `CentredChart.map` declarations move
verbatim to `DiagonalDifferenceFrameData`, publicly imported by the original module.
This avoids an import cycle between the interface and its separate constructions.
All old public imports remain available through that data module. The move changes no
field, body, full name or target meaning. Change record:
`coord/changes/diagonal-difference-frame-data-U1.md`.

Five new theorem modules supply proved intermediate results: the ordered differential
basis, normal-frame construction, centred-chart construction, common-open restriction
uniqueness, and frame change. Their nodes describe the actual proof route.
The chart proof keeps the large pair-map and standard deformation morphism locally
irreducible and uses their chart equations; only the restriction-model identification
unfolds the pair map explicitly. No adopted `WeilConjectures` source file changes. The current source has no Lean
consumer of this module after another group's independent landing. Both
`lem-pur-diagonal-dnc-chart-normalization` and `lem-pur-chart-dnc-square` still cite
this node, so the item is retained and proved. No consumer adaptation is necessary.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.DiagonalDifferenceReesFrame.diagonal_difference_rees_frame`.
Added zero holes. Every new theorem is proved:

- `AlgebraicGeometry.DiagonalDifferenceReesFrame.coordinate_differential_frame`;
- `AlgebraicGeometry.DiagonalDifferenceReesFrame.normal_frame_exists`;
- `AlgebraicGeometry.DiagonalDifferenceReesFrame.centred_chart_exists`;
- `AlgebraicGeometry.DiagonalDifferenceReesFrame.CentredChart.restrict_eq`;
- `AlgebraicGeometry.DiagonalDifferenceReesFrame.frame_change`.

All seven submitted Lean modules compile cleanly through `lcompile.py`; the final
assembly theorem compiled in 30.9 seconds. There are no `sorry`s in these modules. No unfinished statements
are split off. This is a proof from the existing library interfaces, not a relocation
of the original hole. Rank zero and empty schemes require no extra assumptions.

## No longer needed

The main module's direct proof imports are replaced by its four construction and
comparison helpers. Removed direct imports are:
`Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange`,
`Sheaf.AlgebraicGeometry.ConormalConeHomExt`,
`Sheaf.AlgebraicGeometry.EtaleReesChart`,
`Sheaf.RingTheory.ReesAssociatedGradedChart`,
`WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineComparison`,
`WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation`,
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`,
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`,
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Mathlib.AlgebraicGeometry.Morphisms.FlatMono`,
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, and
`Mathlib.AlgebraicGeometry.Pullbacks`.

Most remain used transitively by the existing normal-comparison and Rees interfaces.
In particular `ReesAssociatedGradedChart` remains needed by the unchanged
`ReesConeNormalizedExistence`; its approval is retained. No such source declaration
or dependency is withdrawn.

The separate `lem-pur-dnc-etale-rees-chart` / `Sheaf.AlgebraicGeometry.EtaleReesChart`
route is unnecessary: `SectionReesBaseChange.etale` already gives the geometric
étale map of deformations. The common-principal refinement
`lem-sc-affine-inter-principal-both` is unnecessary for restriction uniqueness:
the actual affine Rees open immersions form a cover and pin every coordinate.
These are route pruning claims, not claims that these nodes have no other consumers.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically valid but duplicates proved library work.
`ChartNormalDifferential` already supplies the centred neighbourhood, normalized
conormal comparison and canonical symmetric comparison.
`SectionReesBaseChangeEtale` supplies the canonical coefficientwise pair map and
its geometric étaleness. Reusing these avoids a new monomial/conormal-base-change
calculation and a separate ring-level étale Rees argument. The positive sign and
both fibre endpoint formulas are still checked explicitly. The blueprint unit route
through the actual diagonal normal frame and deformation chart is preserved.

## New nodes

`def-pur-diagonal-difference-frame-data` attaches the unchanged existing interface
to its data module. See the change record above.

`lem-pur-etale-coordinate-differential-basis` proves the ordered free differential
frame from the polynomial Kähler basis and étale base change.

`lem-pur-diagonal-difference-normal-frame` assembles the positively signed conormal
and normal frame, including comparison independence and rank-zero identities.

`lem-pur-diagonal-difference-centred-chart` constructs the centred neighbourhood,
restriction model and étale deformation map and verifies every endpoint and affine
Laurent formula.

`lem-pur-diagonal-difference-chart-restriction` proves equality on common open
restrictions by their affine Rees charts.

`lem-pur-diagonal-difference-frame-change` proves the inverse matrix equations and
the matching transformation of normal coordinates.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
