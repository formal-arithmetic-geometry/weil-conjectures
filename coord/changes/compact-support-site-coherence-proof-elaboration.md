# AlgebraicGeometry.ProEtale.compactSupportSiteCoherence

## Reason

Server preflight requires a change record for added command-level local transparency
attributes, conservatively classifying these commands as an interface change. They prevent
Lean from unfolding large Kan-extension and derived-functor constructions while checking
this proof. They are all `local`; the backward elaboration options also apply only in this
module. No global attribute, existing signature, public import, or non-theorem body changes.
The original public construction block and final theorem signature were compared verbatim.

## Old

The original section header was:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
```

There were no local reducibility commands or backward-transparency overrides in this file.
All existing declarations retain their original signatures and non-theorem bodies.

## New

The following commands are inserted at the successive proof-calculation boundaries,
in their actual file order (unchanged header commands and declarations are omitted):

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Etale.upperStar Etale.lowerStar upperStar lowerStar
  comparisonUpperStar
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] compactSupportSiteComparisonPlus
  Functor.mapDerivedCategoryPlusCompatibility
  Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
  rightDerivedLowerShriekOfCompactificationPlusCompatibility
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
attribute [local irreducible] compactExchangeTransportComparison properTransportRefinementPlus
attribute [local irreducible] properTransportRefinement
attribute [local implicit_reducible] Etale.rightDerivedLowerShriekPlus rightDerivedLowerShriek
  originCompactSupport comparisonUpperStarPlusEtaleOrigin
attribute [local irreducible] originCompositionModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] coherenceCompactificationChange compactSupportSiteComparison
attribute [local irreducible] Etale.rightDerivedLowerShriekPlusCompIso
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] coherenceEtaleCompositor
  coherenceProEtaleCompositor coherenceCompositionSource
```

The `implicit_reducible` and `irreducible` attributes are explicitly local. They do not
modify the imported constants' exported reducibility attributes. The kernel still checks
every proof; no kernel check is bypassed and no resource limit is raised.
The public construction block is byte-for-byte unchanged. The one existing theorem now
has a complete proof, using only private proved helpers and existing library declarations.
Consequently no target statement or definition meaning changes, and no target statement
review is reopened. There are no forced adaptations or consumer edits in this delivery.

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportSiteCoherence --uses ...` was run for all
public declarations and diagram interfaces. Its 86 downstream modules are listed below,
together with this item. The only downstream textual declaration users are
`Sheaf.Paper.FiniteFreeCompactSupportComposition` and
`Sheaf.Paper.SixFunctorOperationDatumStages`; their uses merely evaluate the unchanged
compositor definitions. The four direct importers and every transitive importer retain
exactly the same public API. Claim holders are those of the shared checkout at preparation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompactSupportSiteCoherence` | U4 | Fill proof; local controls apply only within this file. |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | P4 | No exported interface or definition change; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Uses both compositors, whose types and bodies are unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Uses the pro-étale compositor, whose type and body are unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | No exported interface or definition change; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | No exported interface or definition change; no adaptation. |

## Status

landed 20261020T211838-L-3509904 2026-10-20 (merge of deliver/U4/Sheaf.Paper.CompactSupportSiteCoherence)
