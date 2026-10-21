# AlgebraicGeometry.standardSingleFlatCounit_localization_homology imports

## Reason

Restore the assigned rework module from the exact quarantine path in
`coord/rework.tsv`, preserving its existing zero-hole proof. The unmodified
archive fails against the published library at the `obtain` of the universal
scalar-extension pair: `Tactic generalize failed: result is not type correct`.
Naming that pair before destructuring it gets past elaboration but exposes the
kernel diagnostic `unknown constant ModuleCat.extendScalars_additive_sheaf`.

The minimal repair is a proof-only `import all` of the existing local counit
comparison. With its full interface available, the original `obtain` and the
entire archived proof compile unchanged. No new public instance provider is
needed. Remove the redundant retired `Sheaf.Paper.DerivedHomMayerVietoris`
proof import; `FlatSheafStalk` already publicly imports its upstream provider.

Every byte after `@[expose] public section`, including the theorem signature,
private flatness helper, proof, attributes, options and docstring, equals the
archive. The sole public import is unchanged. No definition, target, adopted
source-library file or mathematical statement is edited. The quarantine archive
and the node's Lean attachment and all four proof dependencies remain intact.

## Old

The source path is absent. The preserved archive is
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationHomology.lean`.
Its complete header is:

```lean
module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk
import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPair
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow
import Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit
import Sheaf.Paper.DerivedHomMayerVietoris
```

## New

Restore
`lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationHomology.lean`
with exactly this header and the unchanged archived declaration text:

```lean
module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk
import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPair
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow
import all Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit
```

## Users

`tools/downstream.py` with `--uses
standardSingleFlatCounit_localization_homology --allow-missing` finds zero live
users because the item is quarantined. A separate import-graph scan of `lean/`
and `quarantine/`, with live sources overriding archives, finds one direct
archived consumer and 93 archived consumers in total. All are listed below.
No consumer is adapted or restored in this delivery. The restored public
statement is verbatim, so their statements and mathematical meanings do not
change. The sole direct consumer is checked separately in the scratch sandbox.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | Direct archived consumer; unchanged theorem and call. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive archived consumer; no interface or meaning change. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive archived consumer; no interface or meaning change. |

## Status

landed 20261021T011013-L-2027639 2026-10-21 (merge of deliver/C4/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology)
