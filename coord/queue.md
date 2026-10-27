# Work queue

289 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 3822 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 0 items.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sf-native-ordinary-chain-currying` | 5017 | none |

## Stage 2: nodes to state (4)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-sf-native-proper-projection-realization` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |

Not open yet: 1135 nodes that below a finished node, not needed, 1 nodes that wait for stage 1 (statement downstream not grounded), 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (283)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 4 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | 15 | 1 | disputed | route |
| `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization` | 18 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 6 | 1 | disputed | 1 |
| `Sheaf.Paper.EtaleScalarPullbackTensorCoherence` | 3 | 1 | proof | route |
| `Sheaf.Paper.NormalizedTateTensorTowerCore` | 3 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 8 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 4 | 8 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 5 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteEtaleSectionIntegration` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionIntegratedSpecialization` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothOrdinaryTwistedCocycles` | 5 | 1 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 6 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionCompletedFinitePull` | 6 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 6 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.BoundedFlatCoefficientSiteSquare` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 7 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare` | 7 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation` | 7 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.ReductionExceptionalChart` | 7 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.ReductionExceptionalRealization` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotients` | 8 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryFinitePull` | 8 | 1 | proof | route |
| `Sheaf.Paper.EtaleOrderedOpenProjectionScalar` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteBundleSectionAdjointScalar` | 8 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorKFlatNormalization` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionSpecializationScalar` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTower` | 8 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 8 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent` | 8 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.SectionScalarBaseChange` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralBoundaryExchange` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralBoundaryRefinementNormalization` | 8 | 1 | proof | route |
| `WeilConjectures.WeilSheaf.VerdierDual` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryPullComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.EtaleOriginRestrictionPullbackCube` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarTensorChainTower` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 1 | proof | route |
| `Sheaf.Paper.RecordedCompactScalarNormalization` | 9 | 1 | proof | route |
| `Sheaf.SixFunctors.CompactSupportRefinementBaseChange` | 9 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelContractions` | 9 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSecondCoordinateContraction` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionComparisonExistence` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportCondition` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalized` | 10 | 1 | proof | route |
| `Sheaf.Paper.RationalP1UnitCounit` | 10 | 3 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExact` | 10 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelUnitCounit` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux` | 11 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelReduction` | 11 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOrigin` | 11 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerEtaleDescent` | 11 | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | 11 | 1 | proof | route |
| `Sheaf.Paper.TraceBaseChangeSecond` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleOpenScalarRestrictionTensor` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | 12 | 1 | proof | route |
| `Sheaf.Paper.NativeOpenSheafTensorExistence` | 12 | 1 | proof | route |
| `Sheaf.Paper.NativeOpenTensorLocalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.NativeOpenTensorNormalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityBaseChange` | 12 | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityScalarReduction` | 12 | 1 | proof | route |
| `Sheaf.Paper.VaryingDimensionDualizingInverse` | 12 | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorRealizationDescent` | 13 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalQuotientClassPullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalQuotientSourcePullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalQuotientTracePullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalScalarPullbackCompatibility` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelDerivedScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangle` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 13 | 15 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransport` | 13 | 1 | proof | route |
| `Sheaf.Paper.RationalP1UnitFactorization` | 13 | 1 | proof | route |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | 13 | 2 | proof | route |
| `Sheaf.Paper.RationalScalarBalancedLocalization` | 13 | 6 | proof | route |
| `Sheaf.Paper.RationalScalarMixedUnitCancellation` | 13 | 6 | proof | route |
| `Sheaf.Paper.SmoothFiniteDualizingInverse` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalHomIdentifications` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierComposition` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierDatum` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierExtension` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierUnit` | 13 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingFunctoriality` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensor` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransport` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedClassPullback` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedTracePullback` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerScalarSquares` | 14 | 1 | proof | route |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForward` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingReverse` | 14 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualNormalization` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | 14 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | 14 | 1 | proof | route |
| `Sheaf.Paper.KummerStrictAdjunctCompatibility` | 14 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSectionProjection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 14 | 2 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 14 | 7 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimit` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingRoosModel` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | 14 | 1 | proof | route |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientInputLaws` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawInput` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawOutputIdentity` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportRealizedScalarTranspose` | 15 | 1 | proof | route |
| `Sheaf.Paper.ConstructibleCompactSupportTargetIso` | 15 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | 15 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralSupportAdjoint` | 15 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicConstantNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChange` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernSplittings` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPretrace` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalRealizationOrdinaryLocalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalRealizationTensorComparison` | 15 | 2 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionQuotientAssociation` | 15 | 1 | proof | route |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | 15 | 3 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingAffineRestriction` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingScalarRealization` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteIntrinsicBidualComparison` | 15 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatDetection` | 16 | 1 | proof | route |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.BoundaryDualizingComposition` | 16 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportScalarEvaluationSquare` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.EtaleQuotientTensorProjection` | 16 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | 16 | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorLocalizationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | 16 | 21 | proof | route |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | 16 | 1 | proof | route |
| `Sheaf.Paper.SystemDirectImageRoosPresentation` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownLevelComparisons` | 17 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownOpenSingletonEvaluation` | 17 | 1 | proof | route |
| `Sheaf.Paper.EtaleSystemProjectionExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportFamily` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | 17 | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 17 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapInvertibility` | 17 | 1 | proof | route |
| `Sheaf.Paper.SfDirectImageRestrictionPasting` | 17 | 1 | proof | route |
| `Sheaf.Paper.WeilIndOpenRealization` | 17 | 1 | proof | route |
| `Sheaf.Paper.WeilIndOpenRepresentability` | 17 | 1 | proof | route |
| `Sheaf.Paper.WeilIndProperHigherRealization` | 17 | 1 | proof | route |
| `Sheaf.Paper.WeilIndProperOpenHigher` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition` | 17 | 1 | proof | route |
| `Sheaf.Paper.BarrettIndRealization` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleSystemRestrictionEvaluation` | 18 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 18 | 2 | proof | route |
| `Sheaf.Paper.FieldShriekCompositionIntegralComponent` | 18 | 1 | proof | route |
| `Sheaf.Paper.FieldShriekCompositionIntegralNaturality` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestriction` | 18 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarFiniteBoundary` | 18 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLift` | 18 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportNormalizedScalarDescent` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalFiniteScalarMates` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | 19 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompositionCoefficientSquare` | 19 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquare` | 19 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralClassPullback` | 19 | 1 | proof | route |
| `Sheaf.Paper.EtaleCofinalSupportComposition` | 20 | 1 | proof | route |
| `Sheaf.Paper.EtaleCofinalSupportRealization` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalProOriginExactLinear` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalProperOpenOriginComparison` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalSiteOriginComparison` | 20 | 1 | proof | route |
| `Sheaf.Paper.TowerReductionMateInvertible` | 20 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare` | 20 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | 20 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjective` | 21 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryComparisonNormalization` | 21 | 1 | proof | route |
| `Sheaf.CategoryTheory.TwistedActionUnderivedRestriction` | 21 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation` | 21 | 1 | proof | route |
| `Sheaf.Paper.SystemOpenRestrictionCoherence` | 21 | 1 | proof | route |
| `Sheaf.Paper.SystemProperRestrictionCoherence` | 21 | 1 | proof | route |
| `Sheaf.Paper.SystemRestrictionFiniteNormalization` | 21 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralCoefficientPullbackExistence` | 21 | 1 | proof | route |
| `Sheaf.Paper.TowerOrdinaryScalarAssociation` | 21 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleRelativelyTrivialLineDescent` | 22 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorCochains` | 22 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedComplexes` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransport` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalEquations` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateResolving` | 23 | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | 23 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberGeometry` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleDiagonal` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedRelativeComparison` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPull` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralExpressionTransposeIsIso` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralProperTowerTransition` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.StructuralReductionWordSubstitution` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjGluedSections` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackLocalComparison` | 25 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionPullTensor` | 25 | 1 | proof | route |
| `Sheaf.SixFunctors.PullQuotientOrdinaryProjection` | 26 | 1 | proof | route |
| `Sheaf.Paper.BasicOperationCoefficientCoherence` | 27 | 1 | proof | route |
| `Sheaf.Paper.BasicOperationReductionAndEvaluation` | 27 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionStrictDerivedSquare` | 27 | 1 | proof | route |
| `Sheaf.Paper.FiniteHomDomainCalculus` | 29 | 2 | proof | route |
| `Sheaf.Paper.FiniteHomIntrinsicTensorComposition` | 29 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionFiniteComponents` | 29 | 1 | proof | route |
| `Sheaf.Paper.FiniteHomOrdinaryTranspose` | 30 | 1 | proof | route |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | 31 | 1 | proof | route |
| `Sheaf.Paper.LocallyClosedInternalAdjunctionIso` | 31 | 1 | proof | route |
| `Sheaf.Paper.LocallyClosedOrdinaryComparisonIso` | 31 | 1 | proof | route |
| `Sheaf.Paper.LocallyClosedPairingCancellation` | 31 | 1 | proof | route |
| `Sheaf.Paper.LocallyProjectiveCoefficientHom` | 31 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedOpenTensorContext` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedQuotientReductionPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComposition` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorFixedCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorRealizationCoefficientsEquality` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTotalTensorIsoComponentEquality` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralTensorPullbackAugmentation` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorIdentification` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportQuotientComputationSquares` | 15 | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 17 | 2 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 2 | proof | 1 |
| `Sheaf.Paper.CondensedCompositorRealization` | - | 1 | proof | 1 |
| `Sheaf.Algebra.Module.GradedLocalizationScalarExtension` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (8)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | 9 | 1 | `lem-pod-rational-purity-pairing` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | 10 | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | 12 | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | 13 | 1 | `lem-per-pulled-quotient-unit-normalization` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
