# WeilConjectures.scalarPullbackOrdinaryNormalization and finite scalar models

## Reason

The profiled item file takes 73--95 seconds when the full finite-model and
normalized ordinary-descent arguments share one module. Local proof interfaces
and the fully proved general descent lemma were insufficient. The brief's
compile-time splitting rule permits extracting the finite-model portion.

## Old

All finite level, strict tower, Roos, good-representative, ordinary derived,
and completed comparison declarations were in
`Sheaf.Paper.IntegralOperationsScalarComparisons`. In particular, the relocated
normalization definition was verbatim:

```lean
def scalarPullbackOrdinaryNormalization {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι X).map
            ((integralDerivedPullbackComparison l E f).hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
            ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullback l L f).map
            ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (integralDerivedPullbackComparison l L f).hom.app
            ⟨_, scalarGood l E L ι Y P⟩
```

## New

The definition displayed above, including its body, is identical in the new file.
Move the finite models through `scalarPullbackOrdinaryNormalization` into
`Sheaf.Paper.IntegralOperationsScalarComparisonModels`. The original module
publicly imports it and retains its original public imports. It also privately
imports the chain-property file's proved naturality helper. The support module keeps the two original public dependencies and publicly
imports ScalarRoosComparison, which re-exports only dependencies already
publicly available through IntegralDerivedOperations.

A parser comparison against the current shared source checks all 46 public
names, every declaration signature, and every definition/abbreviation data
body: all match. Existing public proofs are moved verbatim. No existing exported
instance or elaboration attribute changes. Thus clients still use the same
constants, types, and definitional behavior through the original import.
No other existing Lean module is edited. The substantive proof change is the
ordinary pullback existence/uniqueness proof and its private helpers.

After a 66-second compile of the combined model file, detailed profiling showed
outstanding proof checks at the end of the file. The proved chain naturality
and chain quasi-isomorphism specialization are now in
`Sheaf.Paper.IntegralScalarPullbackChainProperties`, which publicly imports the
finite models for its statement and privately imports the normalized Roos theorem
and generic proof helpers. The original file privately imports
these chain properties. No profiler or trace options remain. This additional
extraction changes no original public declaration, definition body, or consumer.

A subsequent 71-second finite-model compile required separating the generic
Roos construction as well. `Sheaf.Paper.ScalarRoosComparison` now contains the
unchanged `scalarRoosBoundary`, `scalarRoosMap_existsUnique`, and `scalarRoosMap`,
plus the proved generic naturality and tower-assembly helpers. It uses generic
abelian categories and requires no coefficient-specific local instances.
The finite model file publicly re-exports it, and the chain-property proof
privately imports its helpers. The existing additive-Roos node is attached to
this file, so no extra new node or hole is introduced by that extraction.
A fresh parser comparison still confirms all 46 original public signatures
and definition bodies.

The finite models retain all seventeen original private proof imports in their
original order, so their implicit instances elaborate in the original context.
This imports no existing module outside the original item's closure. With this
context, fresh unchanged-consumer checks pass for LocalFrobeniusTransportNormalization
(32.0 seconds) and AdicPurityScalarNaturalityData (53.7 seconds). No consumer
annotation is retained.

The original node keeps the derived declarations; the support node records the
moved finite-model attachments. `def-sf-additive-roos-map` now points to the
actual support file, retaining its declaration names and definition ownership.
No dependency, unit route or quarantined declaration is withdrawn.

The generic strict-tower coordinates are proved directly using the shifted
mapping-cone API. The exploratory private import of
`IntegralAmbientOperationModels` has been removed. The final project import
closure adds only the five new support modules, with no extra existing module.
All new local transparency attributes are scoped to their proof sections;
the aggregate nonlocal instance removals are exactly those of the original item.

## Users

All consumers keep their imports and terms unchanged. An exploratory local
opacity command in AdicPurityScalarNaturalityData passed once but did not
stabilize the timeout (65 seconds in the subsequent module-set check), and is
reverted. No consumer adaptation is included. The public re-export
preserves the original interface; the table includes the 51 direct importers (four live and 47 quarantined at 23:36,
all restored in the live tree at 00:13),
and additional modules textually mentioning the moved names, in the current
source. No consumer signature, data body or proof is adapted. Claim ownership is not
recorded for these modules in the local claim snapshot; the reviewer checks
the server claim records.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicCompletedTensorRealizationDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.AdicHeartPullbackFibres` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CanonicalTateComparisons` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CoefficientDualModelTransport` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CoefficientTensorNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CommonStageFiniteObjectLifting` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CommonStageRestrictionTensorDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CompletedHomScalarTranspose` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CompletedLineComplete` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.EffectiveCompletionPresentationModels` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ExplicitScalarConeWordCoordinates` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FdCompletedCompositorNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FiniteRestrictionCoefficientCore` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.GermReparametrizationDerivedDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.LisseRationalRealizationData` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.MixedReductionUnit` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PodCompletionReindexCoefficientTransition` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PodReindexingRoosComparison` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PodReindexingRoosShiftCompatibility` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PodReindexingStrictComparisons` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointCompositeComparisonTower` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointFibreDerivedTensorCompatibility` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointFibreDerivedTensor` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointIntegralTensorScalarCompatibility` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointPullbackRepresentativeDiagram` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointRationalFamilyCommonStageNaturality` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PointTransformationRationalNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ScalarHomPresentationEvaluation` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SfScalarExtensionComposition` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SourceSectionAutomorphismModel` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SourceSectionIdentityModel` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SourceSectionStalkConeData` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SpecifiedHomScalarEvaluation` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.StrictQuotientStalkReindexing` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.TensorHomExchange` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.TraceStalkCompositorTowerData` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.TraceStalkTowerDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ZlFiniteIntegralFibreReconstruction` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.SixFunctors.OpenRoosRestrictionDescent` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.TraceFormula.IsomorphismQuotientRoosComparison` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.TraceFormula.IsomorphismRoosUnitCancellation` | not recorded locally | Same constants and definitions through the original public import. |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | not recorded locally | Same constants and definitions through the original public import. |

## Status

Open for independent review. All six delivery modules compile in one official
request (`f9aab651b0822ca0c8a388ef`, exit code 0), without warnings. All 51 direct
importers were checked. Across the sweep and fresh clean checks, 41 pass; the
other ten also exceed the limit against the unchanged original item. The report
records each timing comparison. No source error remains after the two initial
missing-object attempts were superseded by actual checks.

Fresh clean checks pass for AdicPurityScalarNaturalityData (53.7 seconds),
LocalFrobeniusTransportNormalization (32.0 seconds), CoefficientDualModelTransport
(54.3 seconds), TraceBoundedQuotientStalkRealization (46.7 seconds),
PointRationalFamilyCommonStageNaturality (12.1 seconds), and OpenRoosUnitAdjunction
(38.9 seconds). All profiling options are removed. Every validation source hash
matches its original, and the unchanged copies are removed from the delivery.
No consumer adaptation is included.
