## What changed

Partial proof delivery of `Sheaf.Paper.IntegralPointTransportTowerPowers`.
All declaration signatures, definitions and public imports are unchanged.

`powerHom` follows by `pow_succ` and the definition of multiplication in `Aut`.
`inverseTower_exact` uses additivity and componentwise finite (co)limit preservation
for right whiskering with the exact sectionwise inverse-image functor.
`ordinarySectionsEvaluation_eq` is definitional equality.
`kappa_isIso` converts intrinsic completeness with `sfDerivedComplete_iff_legacy`,
then uses the two-sided inverse of the actual comparison supplied by
`isomorphismDerivedPullbackComparisonNormalization`.
`pullbackLimitConstructible` transports pullback constructibility along `nu`.
`reductionLimitConstructible` transports constructibility along the specified
completion augmentation `reductionComparison`.

The four new proof imports make the completeness bridge, comparison normalization,
constructibility preservation and invariance under isomorphisms available explicitly.
No new axioms, statements, helpers or split-off holes.

Validation: the final sandbox module compiles cleanly with `lcompile.py`
(exit 0, 32.0 seconds).

## Proved and sorry left

Closed 6 of the original 13 holes (names in namespace
`WeilConjectures.IntegralPointTransportTower`):

- `powerHom`
- `inverseTower_exact`
- `ordinarySectionsEvaluation_eq`
- `kappa_isIso`
- `pullbackLimitConstructible`
- `reductionLimitConstructible`

Added 0 holes. The following 7 original holes remain unchanged, owned by
`lem-trf-integral-point-transport-tower-powers`:

- `WeilConjectures.IntegralPointTransportTower.ordinaryTransport_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.inverseLimitComparison_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.sectionsLimitComparison_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.ordinaryEvaluationComparison_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.integralSigma_existsUnique`
- `WeilConjectures.integralPointTransportTowerPowers`

The two constructibility proofs use existing named comparison theorems that still
have holes; no claim is made that the full module or its transitive axiom closure
is now sorry-free.

## No longer needed

Removed redundant private proof imports (the remaining statements and definitions
retain the original public imports):

- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.Paper.IntegralInverseImageComparisonComposition`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.PointProEtaleSectionsExact`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.SixFunctors.FrobeniusPointTransport`

No modules withdrawn and no mathematical DAG nodes pruned. The existing assembly
plan remains needed for the unfinished main theorem, so its proof dependencies
are retained. No source-library declarations or public imports were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The main DAG describes an assembly through alternative
reindexing and Roos presentations; identifying those presentations with the
specified tensor-model constructions remains part of the unfinished assembly.
The elementary helper proofs above do not require that assembly.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
