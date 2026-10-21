# AlgebraicGeometry.standardSingleFlatCounit_localization_pair

## Reason

Restore the assigned source from the exact quarantine path in `coord/rework.tsv`:
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationPair.lean`.
The archive already has a complete proof and zero holes. Against the current
published build it fails at line 35: Lean cannot synthesize
`(ModuleCat.extendScalars (g.stalkMap a).hom).Additive` for the homotopy functor
in the public theorem statement. The resolution-theorem application at line 48
also fails to synthesize additivity for the corresponding algebra map, followed
by a consequent type error in its returned witnesses.

Explicitly publicly import the existing provider of the proved instance
`ModuleCat.baseDerivedTensor_extendScalars_additive`. Additivity occurs in the
public statement through `mapHomotopyCategory`, so this is a public dependency.
The theorem signature, proof, universes, docstring and attributes are verbatim
from the archive. No definition or target type changes. No source-library file
or declaration is edited. The original archive remains intact.

The repaired module compiles cleanly through `lcompile.py` in 4.2 seconds, and
an independent `#print axioms` probe reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The import-direction check permits the
new import. This repairs the observed compilation failure rather than merely
restoring a failing copy or rebasing an earlier delivery.

## Old

The source path is absent. The preserved archive begins:

```lean
module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
```

## New

Restore `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationPair.lean`
with this one added public import; every remaining byte equals the archive:

```lean
module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
```

## Users

`tools/downstream.py` with `--uses standardSingleFlatCounit_localization_pair
--allow-missing` reports zero live importers and zero live declaration users.
A source scan of both `lean/` and `quarantine/`, with live modules overriding
archives, finds one direct archived consumer and 93 further transitive archived
consumers. They are listed below. Restoring the original theorem and adding an
existing proved instance changes none of their hypotheses, conclusions or data.
No consumer is adapted or restored in this delivery.

The unchanged direct consumer `StandardSingleFlatCounitLocalizationHomology`
was checked against the repaired root. It independently fails in its own public
statement at archived lines 83 and 97 because its scalar-extension additivity
instance is also unavailable. Its import of this item is private, so this
consumer needs its own explicit public instance-provider import when restored.
This failure precedes its call to the restored theorem and is not caused by a
signature change. A separate scratch check adds that provider to the consumer
while retaining its original statement and proof; results are recorded in the
worker report. Scratch files are not delivered. Its rework remains separate.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology | unclaimed | Direct archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive archived consumer; theorem type and proof unchanged. |

## Status

landed 20261021T004814-L-1789607 2026-10-21 (merge of deliver/B4/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPair)
