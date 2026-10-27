# Strict-tower compact-support interface extraction

## Reason

The item must import the existing normalized comparison realization to assemble
its laws. That dependency reaches the item through the public import in
`Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData`, creating a cycle.
Move the unchanged tower declarations R through Laws into
`Sheaf.Paper.SmoothPurityTowerShriekData`, publicly reexport them from the item,
and redirect the comparison data module's one public import to that shared module.

Repair of returned head `6f1f7ab3b2a`: current main incorporated F4's
`b59b636ad25`, which proved the comparison realization and extracted its interfaces.
The previous 753-line sandbox copy would overwrite that work. It is replaced by
the current 133-line proved module, byte for byte. The sole adaptation is now the
one-line import change in the newly extracted comparison data module. No proof or
signature from F4's delivery is changed. Both comparison modules have no holder
in the published claim mirror at the repair check; F4 is the author of the landed
proof, not a newly claimed adaptation target.

No source-library file is changed. Every existing declaration signature, body,
instance and attribute in the relocated tower interface remains unchanged. Source
comparison ignoring comments confirms this against current main. The target
statements and their meanings remain unchanged.

## Old

```lean
-- Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData, current main:
public import Sheaf.Paper.SmoothPurityTowerShriekLevels

-- The item, with the interface declarations R through Laws preceding this theorem:
theorem tower_shriek_levels :
    ∃ b : Base l E, ∃ o : Operations l E b, ∃ x : OpenExchange l E b o,
      Laws l E b o x := by
  sorry
```

The complete old tower interface is retained verbatim, except docstring blueprint
attachments, in `SmoothPurityTowerShriekData.lean`; its declarations are attached to
`def-sp-tower-shriek-data`.

## New

```lean
-- Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData:
public import Sheaf.Paper.SmoothPurityTowerShriekData

-- Sheaf.Paper.SmoothPurityTowerShriekLevels:
public import Sheaf.Paper.SmoothPurityTowerShriekData
import Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization
import Sheaf.Paper.SmoothPurityFiniteLevelProjectionCriterion
import Sheaf.Paper.SmoothPurityTowerLocalization
import Sheaf.Paper.SmoothPurityTowerExchange
```

The item proves the same theorem by assembling boundedness, joint conservativity,
projection invertibility and the separate exchange and localization residuals.
The three new residual theorem modules isolate finite projection invertibility,
localization of the strict counit-unit sequence, and the exchange field. None
asserts existence of the entire calculus.

The comparison-data import ceases to reexport `tower_shriek_levels`. The only
external executable Lean use of that theorem is
`Sheaf.Paper.CoefficientTowerShriekCalculus`, which explicitly publicly imports
the item. `TowerP1ProperCtf` also mentions it in proof prose only. All other names remain publicly visible through the shared interface.
No consumer adaptation is required. An overlay import-graph check of 10,254
reachable project modules found no cycle.

## Users

The table lists the current transitive consumers reported by
`tools/downstream.py SmoothPurityTowerShriekLevels
SmoothPurityStrictCompactificationComparisonData --names`, plus the changed roots.
No unrelated consumer is edited. All declaration bodies and names remain identical;
consumers need no mathematical adaptation. The claims below refer to the published
claim mirror at repair time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationOpenLimit | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationPushLimit | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationScalarData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalBaseSquares | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCompletedFrame | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalCompletedPushSquare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalFiniteRootMap | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalIntegralRootMap | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalQuotientBaseChange | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTracePresentationExistence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTraceResultExistence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalTraceSources | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.DiagonalUniformizerAnnihilator | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTowerData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerGeometryLimits | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RationalTatePullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RestrictionLocal | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData | No holder in published claim mirror | One public import redirected to the shared tower interface; declarations unchanged. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization | No holder in published claim mirror | Unchanged proved F4 assembly; current main copied verbatim. |
| Sheaf.Paper.SmoothPurityStrictFiniteWordIdentification | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictOpenWordEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictPlusComparisonsRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictPlusEvaluationRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictSystemGeometricRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerFibreProjections | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S2, dispatched item | Same theorem and public interface; proof assembled. |
| Sheaf.Paper.TateTwistedProjection | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerChernPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerChernRealizationPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassChern | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassFinite | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassProjective | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassSystems | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerIntegralClassPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Targets.PoincareUncurry | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| TargetsCheck | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.Statement | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Basic | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Main | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Product | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.Statement | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | No holder in published claim mirror | Existing names, signatures and bodies preserved through public reexport; no adaptation. |

## Status

landed 20261025T203044-L-2779831 2026-10-25 (merge of deliver/S2/Sheaf.Paper.SmoothPurityTowerShriekLevels)
