## What changed

Proved `completedOrdinaryReductionPullbackInv_isIso` by identifying the ordinary
pullback map with the conjugate of the already invertible restriction pullback
comparison, using the mate equivalence and its two-sided inverse. The canonical
completed tower evaluation is imported from `Sheaf.Paper.CompletedTowerDirectImage`
and used as the witness for the remaining evaluation existence statement.

## Proved and sorry left

Closed:

- `completedOrdinaryReductionPullbackInv_isIso`.

The following five theorem declarations still contain their original proof holes:

- `AdicCoefficientDatum.towerPushEvaluation_existsUnique` (model equation and uniqueness);
- `AdicCoefficientDatum.directImageRlim_roos`;
- `completedReductionLevelPullbackIso_transition`;
- `completedReductionPullbackIso_existsUnique`;
- `AdicCoefficientDatum.towerProjection_properties`.

No new sorry declarations were added.

## No longer needed

The proof does not use the following former proof-only imports, which were removed:

- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`;
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`;
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`;
- `Sheaf.CategoryTheory.DiagramSiteRealization`;
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`;
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`;
- `Sheaf.Paper.AdicCoefficientDatum`;
- `Sheaf.Paper.CompletedDerivedInverseLimit`;
- `Sheaf.Paper.IntrinsicCompletionCompleted`;
- `Sheaf.Paper.KoszulReconstruction`;
- `Sheaf.Paper.PerfectProjectionFormula`;
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`;
- `Sheaf.Paper.ProjectionMateExact`;
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
- `WeilConjectures.Algebra.Homology.RoosComplex`.

## Where the brief, the DAG or earlier work was wrong

The evaluation declaration's existing canonical comparison has the required
map-derived-category type only after its completed tower aliases are unfolded;
the direct-image module therefore needs the proof-only import
`Sheaf.Paper.CompletedTowerDirectImage` to use that canonical witness.

## New nodes

None.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
