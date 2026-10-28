# Work queue

266 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 684 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 2, stage 3 6 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (7)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-pur-system-scalar-associator-coherence` | 1 | state | 0 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |
| `lem-pur-integral-scalar-reduction-intertwining` | 2 | state | 0 |
| `lem-pur-scalar-reduction-transpose-normalization` | 2 | state | 0 |

Not open yet: 1134 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (258)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 11 | 1 | disputed | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward` | - | 1 | disputed | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization` | - | 1 | disputed | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | - | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 6 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.InverseImageRingFunctor` | 9 | 1 | proof | route |
| `Sheaf.CategoryTheory.RouteInverseImageConstantComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientTwistsDetailed` | 9 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 9 | 6 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation` | 10 | 1 | proof | route |
| `Sheaf.Paper.CanonicalRationalPullbackTensorCompositionLeftLocalization` | 11 | 1 | proof | route |
| `Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization` | 11 | 1 | proof | route |
| `Sheaf.Paper.CommonStageInternalHomRepresentative` | 11 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso` | 11 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackTensorCompositionReduced` | 11 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative` | 11 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitExistence` | 11 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitUniqueness` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 12 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives` | 12 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientPullbackFiniteIso` | 13 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientSequencePullbackIso` | 13 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackDerivedCompositionLaws` | 13 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsCore` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsScalarHomZero` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinal` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedEvaluationProjection` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionCore` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionNormalizations` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorAssociativity` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorHorizontal` | 13 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerTransitionSquare` | 13 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorDerivedHomologyComparison` | 16 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorModelHomologyIdentification` | 16 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicCoordinateTransitions` | 17 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackLeftRoos` | 17 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackRightRoos` | 17 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly` | 17 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicLiftedTransitionTranspose` | 18 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel` | 18 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackRoosCoordinates` | 18 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerScalarRestriction` | 19 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction` | 20 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientRealizationHomologyLift` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModelComparison` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModelProperties` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleStalkFromLocal` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedActual` | 20 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedConstants` | 20 | 1 | proof | route |
| `Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCoreAfterIdentity` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologyChosenGeometricFibreData` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelSquares` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonPrefix` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonSymmetry` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCanonicalIdentity` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistMultiplication` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistSectionRestriction` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentObject` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransition` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeHomSignedShiftLaws` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit` | - | 1 | proof | route |
| `Sheaf.Paper.AdicIntegralReindexingMaps` | - | 1 | proof | route |
| `Sheaf.Paper.AdicRealizationComparisonDescent` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensorIntegral` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingUnitContraction` | - | 1 | proof | route |
| `Sheaf.Paper.AffineSpaceIsoTraceInvariance` | - | 1 | proof | route |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | - | 3 | proof | route |
| `Sheaf.Paper.CanonicalCoefficientCompositionLaws` | - | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | - | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorOrdinaryCounit` | - | 1 | proof | route |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | - | 1 | proof | route |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalIsoFamily` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedScalarAssociatorLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | - | 4 | proof | route |
| `Sheaf.Paper.DiagonalCompletedAdjunctSquare` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalFiniteUnitPush` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceRootProjection` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | - | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | - | 3 | proof | route |
| `Sheaf.Paper.ExceptionalRationalNormalizedScalarShift` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCorePostData` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreReconstruction` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparisonBeta` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparisonFlatness` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteP1OrdinaryKummerBoundary` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponentCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientDerivedDetection` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinatesCore` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackChainSquareComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FrobeniusIntegralRootTransport` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 11 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | - | 2 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonRepresentative` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonUncurry` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerAugmentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerTransition` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomTensorPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralRootPowerGenerators` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpointInverseImage` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpointMate` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackUnitsEndpointCanonical` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting` | - | 2 | proof | route |
| `Sheaf.Paper.IsomorphismScalarCompletedModelFormula` | - | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarCompletedPreservesModels` | - | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula` | - | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas` | - | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteTransitionFormulas` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicFunctorDescent` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChangePresentation` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChangeSquare` | - | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionData` | - | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality` | - | 1 | proof | route |
| `Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainLaws` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatFlat` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedUnderivedIso` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingComparisonCore` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedComparisonsCore` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingEvaluationLaw` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 20 | proof | route |
| `Sheaf.Paper.PodReindexingReductionTensorSquareDescent` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingShiftChainPart` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingShiftDerivedPart` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingStrictTensorTowers` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorFamilyIdentityComposition` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorFamilyTensorConstraints` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorLimitModelDescent` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorRoosNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedShiftsCore` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedSquares` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSubstitutionCore` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceArrow` | - | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.QcqsCompletedRefinement` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlatDerived` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlatOrdinary` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCore` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChernSome` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjectionNative` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchangeCore` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchangeTail` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | - | 2 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarP1UnitMateComponent` | - | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | - | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateRhsCore` | - | 1 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | - | 7 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralUnitNormalizationComponents` | - | 1 | proof | route |
| `Sheaf.Paper.TowerScalarRootAbelianTransposeCore` | - | 1 | proof | route |
| `Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized` | - | 1 | proof | route |
| `Sheaf.SixFunctors.AffineRestrictionMapIso` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent` | - | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactCommShift` | - | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactShiftData` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingQuotientNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRestrictionTransport` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportBridge` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonicalMate` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportIntrinsicMate` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingBaseChange` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryBasicSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 2 | proof | route |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | - | 1 | proof | route |
| `Sheaf.TraceFormula.CanonicalRelativeProjProperLocal` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit` | 13 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw` | 16 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 2 | proof | 1 |
| `Sheaf.Paper.FiniteHomDomainCalculus` | - | 2 | proof | 1 |
| `Sheaf.Paper.FiniteProperComparisonIso` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralAutomorphismCancellationNormalization` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralCompactSupportRestrictionShift` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 2 | proof | 1 |
| `Sheaf.Paper.RationalBraidingScalarCompatibility` | - | 1 | proof | 1 |
| `Sheaf.Paper.RationalConstantUnitFrobenius` | - | 1 | proof | 1 |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralBraidingNaturality` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralBraidingScalarExtensionSquare` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackTensorAssociatorNaturality` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (7)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 10 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.RationalTensorAssociatorScalarSquare` | - | 1 | `lem-pur-integral-scalar-reduction-intertwining` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 1 | `lem-pur-composition-comparison-scalar-compatibility` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | - | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | - | 1 | `lem-pod-rational-purity-pairing` |
