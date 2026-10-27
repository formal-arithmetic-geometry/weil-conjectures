## What changed

Filled `AlgebraicGeometry.isOpenImmersion_and_quasiCompact_of_canonical_affine_charts`
in `Sheaf.AlgebraicGeometry.CanonicalAffineChartsQcOpenImmersion`, with its signature
and public imports unchanged. Substituting the structure-map equality identifies
all source opens with actual inverse images under `c`. On each affine base open,
the chart equality and cancellation of an open immersion give the restricted
open immersion. The quasi-affine source is compact and the affine target is
quasi-separated, giving quasi-compactness. The pulled-back affine opens cover
`Y`. Injectivity of their restrictions gives global injectivity, and the stated
injective local-source criterion gives the global open immersion. Target locality
then gives global quasi-compactness. This follows all five steps of the existing
node; no DAG route change or additional dependencies are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isOpenImmersion_and_quasiCompact_of_canonical_affine_charts`
(node `lem-trf-canonical-affine-charts-qc-open-immersion`). No holes remain and
no holes or declarations were added. No split-off results. The proof uses Mathlib
alone. Its argument permits empty schemes and arbitrary, possibly noncompact or
nonseparated bases: it chooses an affine neighbourhood for each target point and
never takes a finite subcover.

## No longer needed

Removed four redundant private imports, all already available through the
unchanged public imports: `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.AlgebraicGeometry.Morphisms.Basic`, and
`Mathlib.AlgebraicGeometry.AffineScheme`. Their declarations are still used through
those public imports. No DAG nodes or project modules are pruned; every stated
proof dependency is used.

## Where the brief, the DAG or earlier work was wrong

None. The existing mathematical statement, proof plan and unit route are retained.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
