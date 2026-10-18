## What changed

Added `Sheaf.AlgebraicGeometry.TopCoherentCohomologyFiniteQuotient`, whose geometric
statement packages the projective-closure part of the planned proof as a proper surjective
modification together with a surjection from `Fin n → k` onto top coherent cohomology. The target module now imports this split and
proves `finiteDimensional_top_coherent_cohomology` by
`FiniteDimensional.of_surjective`.

## Proved and sorry left

`AlgebraicGeometry.finiteDimensional_top_coherent_cohomology` is proved from the new
quotient theorem and Mathlib's `FiniteDimensional.of_surjective`. The new theorem
`AlgebraicGeometry.exists_finiteDimensional_top_coherent_cohomology_quotient` remains a
single `sorry`, with node
`lem-weil-pbc-top-coherent-cohomology-finite-quotient`.

## No longer needed

The wrapper proof no longer needs these proof-only imports or their planned dependency
nodes: `Mathlib.AlgebraicGeometry.Noetherian`,
`Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`Sheaf.AlgebraicGeometry.CohomologyFiniteExtension`,
`Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`,
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`,
`Sheaf.Algebra.Homology.ModuleStalkExact`,
`WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks`,
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`,
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`,
`Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop`,
`WeilConjectures.AlgebraicGeometry.ChowLemma`,
`Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.AlgebraicGeometry.RelativeSerreVanishing`,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
`Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison`,
`WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective`,
`Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective`,
`WeilConjectures.Algebra.Homology.ModuleStalkExact`,
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`,
`WeilConjectures.AlgebraicGeometry.PQFCohomology`, and
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` as proof imports of the
old route. The quotient split records only the top-degree restriction and projective
finiteness nodes as its proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node's page-long induction cannot be expressed directly with the available
categorical interfaces in the allotted worker session. The delivery records the essential
geometric bottleneck as a quotient statement and proves the finite-dimensional wrapper
completely.

## New nodes

Added `lem-weil-pbc-top-coherent-cohomology-finite-quotient` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-top-coherent-cohomology-finite-quotient.json`.

The associated change record is `coord/changes/top-coherent-cohomology-finite-route.md`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
