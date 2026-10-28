# Work queue

329 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 391 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 0 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (11)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-sp-ctf-tower-pullback-reconstruction` | 1 | state | 1 |
| `lem-pur-system-scalar-associator-coherence` | 1 | state | 0 |
| `lem-pur-tower-purity-ground-field-retagging` | 1 | state | 0 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |
| `lem-pur-composition-comparison-scalar-compatibility` | 2 | state | 0 |
| `lem-pur-integral-scalar-reduction-intertwining` | 2 | state | 0 |
| `lem-pur-rational-normalized-purity-diagrams` | 2 | state | 0 |
| `lem-pur-scalar-reduction-transpose-normalization` | 2 | state | 0 |

Not open yet: 1131 nodes that below a finished node, not needed, 3 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (317)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 2 | disputed | route |
| `Sheaf.SmoothPurity.TraceExistence` | 1 | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 7 | 1 | disputed | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | disputed | route |
| `Sheaf.SixFunctors.RationalVerdierDatumNaturality` | 14 | 1 | disputed | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization` | 15 | 1 | disputed | route |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | 18 | 1 | disputed | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | 21 | 1 | disputed | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward` | - | 1 | disputed | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | - | 1 | disputed | 2 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 6 | proof | route |
| `Sheaf.Paper.CoefficientTwistsDetailed` | 5 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 6 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | 6 | 1 | proof | route |
| `Sheaf.Paper.CanonicalRationalPullbackTensorCompositionLeftLocalization` | 7 | 1 | proof | route |
| `Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization` | 7 | 1 | proof | route |
| `Sheaf.Paper.CommonStageInternalHomRepresentative` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackTensorCompositionReduced` | 7 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative` | 7 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitExistence` | 7 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitUniqueness` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.InverseImageRingFunctor` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.RouteInverseImageConstantComparison` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness` | 9 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientPullbackFiniteIso` | 9 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientSequencePullbackIso` | 9 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackDerivedCompositionLaws` | 9 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsCore` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsScalarHomZero` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinal` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedEvaluationProjection` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionCore` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionNormalizations` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorAssociativity` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorHorizontal` | 9 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerTransitionSquare` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation` | 9 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports` | 10 | 1 | proof | route |
| `Sheaf.Paper.AffineSpaceIsoTraceInvariance` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso` | 10 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactProjectionFormulaTheorem` | 10 | 1 | proof | route |
| `Sheaf.WeilSheaf.CoefficientCohomologyComparison` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit` | 11 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso` | 11 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportLocalization` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactCommShift` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactShiftData` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelFirstAmbientFormula` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelFirstTransport` | 11 | 1 | proof | route |
| `Sheaf.WeilSheaf.SmoothCoefficientVanishing` | 11 | 1 | proof | route |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | 12 | 1 | proof | route |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 11 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicFunctorDescent` | 12 | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor` | 12 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlatDerived` | 12 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlatOrdinary` | 12 | 1 | proof | route |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | 12 | 6 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 12 | 7 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical` | 13 | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | 13 | 3 | proof | route |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | 13 | 7 | proof | route |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | 13 | 3 | proof | route |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | 13 | 4 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinatesCore` | 13 | 1 | proof | route |
| `Sheaf.Paper.FrobeniusIntegralRootTransport` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | 13 | 2 | proof | route |
| `Sheaf.Paper.IntegralRootPowerGenerators` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerScalarRestriction` | 13 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackLeftRoos` | 13 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackRightRoos` | 13 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly` | 13 | 1 | proof | route |
| `Sheaf.Paper.CommonStagePullbackCompNaturality` | 14 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction` | 14 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientRealizationHomologyLift` | 14 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion` | 14 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModelComparison` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModelProperties` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleStalkFromLocal` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedActual` | 14 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedConstants` | 14 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator` | 14 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | 14 | 20 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 14 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | 14 | 2 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackRoosCoordinates` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalDualFormulaScalarCounit` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierCompositionEquation` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingIdentity` | 15 | 1 | proof | route |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA` | 15 | 8 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonRepresentative` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomEvaluationTransport` | 15 | 2 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChangePresentation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChangeSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.QcqsCompletedRefinement` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityE` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalDualFormulaAdjunction` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierScalarInterchange` | 15 | 1 | proof | route |
| `Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents` | 16 | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary` | 16 | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeHomSignedShiftLaws` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicIntegralReindexingMaps` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicRealizationComparisonDescent` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCompositionCancelled` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensorIntegral` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingUnitContraction` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | 16 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorDerivedHomologyComparison` | 16 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorModelHomologyIdentification` | 16 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonUncurry` | 16 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionPresentation` | 16 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomTensorPresentation` | 16 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted` | 16 | 1 | proof | route |
| `Sheaf.Paper.PodIntegralHomComparisonIsIso` | 16 | 1 | proof | route |
| `Sheaf.Paper.PodIntegralHomComparisonNaturality` | 16 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceArrow` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded` | 16 | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | 16 | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.AffineRestrictionMapIso` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | 16 | 5 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionPureTensor` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionTranspose` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierShift` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingQuotientNormalization` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerLimit` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAt` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCoreAfterIdentity` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelSquares` | 17 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 3 | proof | route |
| `Sheaf.Paper.ExceptionalRationalNormalizedScalarShift` | 17 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparisonBeta` | 17 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparisonFlatness` | 17 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicCoordinateTransitions` | 17 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerAugmentation` | 17 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerTransition` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChernSome` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjectionNative` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchangeCore` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchangeTail` | 17 | 1 | proof | route |
| `Sheaf.Paper.ScalarP1UnitMateComponent` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRestrictionTransport` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierEvaluationDetection` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonPrefix` | 18 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonSymmetry` | 18 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit` | 18 | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence` | 18 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalCoherence` | 18 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalIsoFamily` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedAdjunctSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicLiftedTransitionTranspose` | 18 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel` | 18 | 1 | proof | route |
| `Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingComparisonCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedComparisonsCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingEvaluationLaw` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingShiftChainPart` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingShiftDerivedPart` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingStrictTensorTowers` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorCoefficientTransitionCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorCoefficientTransitionTensor` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorFamilyIdentityComposition` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorFamilyTensorConstraints` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorLimitModelDescent` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorRoosNormalization` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedShiftsCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedSquares` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSubstitutionCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementRestrictionComponentShift` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingBaseChange` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical` | 18 | 1 | proof | route |
| `Sheaf.Paper.CompletedScalarAssociatorLocalization` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem` | 19 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingReductionTensorSquareDescent` | 19 | 1 | proof | route |
| `Sheaf.Paper.RefinementProperCounitIsIso` | 19 | 2 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportBridge` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryBasicSquare` | 19 | 1 | proof | route |
| `Sheaf.Paper.CanonicalCoefficientCompositionLaws` | 20 | 1 | proof | route |
| `Sheaf.Paper.DiagonalFiniteUnitPush` | 20 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed` | 20 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceRootProjection` | 20 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCorePostData` | 20 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1OrdinaryKummerBoundary` | 20 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientDerivedDetection` | 20 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent` | 20 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportIntrinsicMate` | 20 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence` | 21 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreReconstruction` | 21 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence` | 21 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonicalMate` | 21 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition` | 21 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorOrdinaryCounit` | 22 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionData` | 22 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality` | 22 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | 22 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence` | 22 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality` | 22 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarCompletedModelFormula` | 23 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarCompletedPreservesModels` | 23 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula` | 24 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas` | 24 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteTransitionFormulas` | 24 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainLaws` | 24 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatFlat` | 24 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedUnderivedIso` | 24 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralUnitNormalizationComponents` | 24 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarRootAbelianTransposeCore` | 24 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized` | 24 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpointInverseImage` | 25 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpointMate` | 25 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackUnitsEndpointCanonical` | 25 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence` | 25 | 1 | proof | route |
| `Sheaf.TraceFormula.CanonicalRelativeProjProperLocal` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistMultiplication` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCanonicalIdentity` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistSectionRestriction` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentObject` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransition` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologyChosenGeometricFibreData` | 30 | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponentCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackChainSquareComponent` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting` | - | 2 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateRhsCore` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 2 | proof | route |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit` | 11 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteProperComparisonIso` | 13 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralCompactSupportRestrictionShift` | 13 | 1 | proof | 1 |
| `Sheaf.Paper.RationalConstantUnitFrobenius` | 13 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw` | 14 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralAutomorphismCancellationNormalization` | 14 | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 15 | 2 | proof | 1 |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | 18 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteHomDomainCalculus` | 22 | 2 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic` | 28 | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 5 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 2 | proof | 1 |
| `Sheaf.Paper.NativeProperProjectionRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.RationalBraidingScalarCompatibility` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralBraidingNaturality` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralBraidingScalarExtensionSquare` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackTensorAssociatorNaturality` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (12)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | 9 | 1 | `lem-pod-rational-purity-pairing` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | 12 | 4 | `lem-pur-tower-purity-ground-field-retagging` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | 12 | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `Sheaf.Paper.IteratedPurityScalarPasting` | - | 2 | `lem-pur-rational-normalized-purity-diagrams` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `Sheaf.Paper.RationalTensorAssociatorScalarSquare` | - | 1 | `lem-pur-integral-scalar-reduction-intertwining` |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 1 | `lem-pur-composition-comparison-scalar-compatibility` |
