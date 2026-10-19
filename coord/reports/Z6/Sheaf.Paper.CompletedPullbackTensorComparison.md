## What changed

Completed eight proofs and removed 25 unused proof imports in `Sheaf.Paper.CompletedPullbackTensorComparison`.
The node records these proof components and their existing dependencies.
The proof now imports `Sheaf.Paper.IntegralComparisonSequenceSystems` for the existing
sequence-site construction. It proves sequence continuity and ring-map uniqueness,
identifies the sequence direct image with the existing construction and derives its
right adjoint and exact inverse image, proves ordinary additivity, establishes the Roos
augmentation condition from limit projection compatibility, constructs the finite
intrinsic pullback comparison from adjunction uniqueness, and constructs the rational
comparison by localizing the integral comparison and using the prescribed object formulas.

## Proved and sorry left

Closed: `WeilConjectures.pullbackTensorSequenceBase_continuous`,
`WeilConjectures.pullbackTensorSequenceRing_existsUnique`, `WeilConjectures.pullbackTensorSequenceDirect_rightAdjoint`,
`WeilConjectures.pullbackTensorSequenceInverse_exact`, `WeilConjectures.pullbackTensorOrdinary_additive`,
`WeilConjectures.pullbackTensorRoosAugmentation_condition`, `WeilConjectures.pullbackTensorLevelIntrinsic_existsUnique`,
and `WeilConjectures.canonicalRationalPullbackTensor_existsUnique` (8 sorries).

Added holes: none. No existing signature or public import changed.
The retained proof compiled cleanly against the published library in 35.8 seconds.

The module retains the following 27 existing named sorries, all attached to
`def-pur-completed-pullback-tensor-comparison`; no new sorry was added.

- `WeilConjectures.pullbackTensorOrdinaryLimit_rightAdjoint`
- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceDirectEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
- `WeilConjectures.pullbackTensorComparisonCounits`
- `WeilConjectures.pullbackTensorDerivedEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`
- `WeilConjectures.pullbackTensorFiniteGood`
- `WeilConjectures.pullbackTensorQuotient_existsUnique`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

Removed the following 25 unused proof imports. Their planned proof APIs are not used
by the eight completed proofs; required statement APIs remain available through the
unchanged public imports and the sequence-system import.

- `Sheaf.Paper.NormalizedDVRTower`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`

No whole module or node is claimed to leave the targets' import closure: other public
imports still reach these dependencies. The original node had no proof steps or proof
dependencies to prune. The remaining named obligations retain their existing docstring
plans and signatures.

## Where the brief, the DAG or earlier work was wrong

The retained proof had an invalid call to the augmentation theorem with a function where a
functor was required, and an invalid extensionality step for opposite objects. Both were
replaced by direct limit-projection compatibility and the correct opposite-object
components. The earlier proof also imported `IntegralTensorPullback` solely for that invalid
call; that import was removed.

The sequence-system node `def-trf-integral-comparison-sequence-systems` is used as a tool
from another unit because it supplies the identical sequence-site base change, coefficient
map and module adjunction already defined by this module. The item's unit has no realized
proof steps to bypass. The import-direction check confirmed that it introduces no cycle.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
