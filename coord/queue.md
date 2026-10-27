# Work queue

228 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 119 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 0 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (10)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-route-inverse-image-constant-comparison` | 1 | state | 0 |
| `lem-route-inverse-image-module-lift` | 1 | state | 0 |
| `lem-route-inverse-image-ring-functor` | 1 | state | 0 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-sf-native-proper-projection-realization` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |
| `lem-pur-composition-comparison-scalar-compatibility` | 2 | state | 0 |
| `lem-pur-rational-normalized-purity-diagrams` | 2 | state | 0 |

Not open yet: 1133 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (217)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 4 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 8 | 1 | disputed | route |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | 14 | 1 | disputed | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 15 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 7 | 1 | disputed | 1 |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | - | 1 | disputed | 3 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 7 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 6 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 6 | 1 | proof | route |
| `Sheaf.Paper.RestrictionTensorRepresentativeTransport` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | 6 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemResolutionModels` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPull` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotientsFlatness` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotientsProjection` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotientsQuotient` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryFinitePullUniqueness` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTowerComponent` | 9 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 9 | 1 | proof | route |
| `Sheaf.Paper.ProperBaseChangeAdmissibleGenerators` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 2 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | 9 | 1 | proof | route |
| `Sheaf.WeilSheaf.SmoothDualizingCohomology` | 9 | 1 | proof | route |
| `Sheaf.WeilSheaf.SmoothDualizingConcentration` | 9 | 1 | proof | route |
| `Sheaf.Paper.RationalP1UnitCounit` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose` | 11 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionDerivedComparisonExistence` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportExtension` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportKFlat` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedBarB` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedPure` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedTotal` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 2 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelExtensionIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 15 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | 12 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleDescent` | 12 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore` | 12 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport` | 12 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerEtaleNormalizationDescent` | 12 | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | 13 | 2 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence` | 13 | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChange` | 13 | 1 | proof | route |
| `Sheaf.Paper.RationalP1UnitFactorization` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | 13 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLift` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorFiniteModelExistence` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingFunctoriality` | 14 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensor` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparisonData` | 14 | 2 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransport` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerScalarSquares` | 14 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelCoefficientTransport` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelConstantScalarExtensionCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerLocalComplexCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexesAux` | 14 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism` | 14 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportScalarMateInvertible` | 14 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 1 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | 14 | 1 | proof | route |
| `Sheaf.Paper.VectorIntegrationCartesianTrace` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForwardBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualLevels` | 15 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualRealization` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport` | 15 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveCanonicalSectionProjection` | 15 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPretrace` | 15 | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | 15 | 1 | proof | route |
| `Sheaf.Paper.StrictKummerUnitNormalization` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenFlatDetection` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralData` | 16 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarModelExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.ConstructibleCompactSupportTargetIsoStage` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalEvaluationUnit` | 16 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicConstantCoherence` | 16 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicConstantUniversal` | 16 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | 16 | 21 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChern` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernP2Splitting` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQSplitting` | 16 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitSquare` | 16 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquare` | 16 | 1 | proof | route |
| `Sheaf.Paper.SfDirectImageRestrictionPasting` | 16 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit` | 16 | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison` | 17 | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates` | 17 | 1 | proof | route |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA` | 17 | 9 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingOperationsExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCore` | 17 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinement` | 17 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapOpenUnit` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionData` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionIsIso` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionShift` | 18 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarFiniteBoundary` | 18 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | 19 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence` | 19 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftUniqueness` | 19 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative` | 20 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary` | 20 | 1 | proof | route |
| `Sheaf.CategoryTheory.TwistedActionUnderivedRestriction` | 21 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluationComponent` | 21 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorFiniteExistence` | 22 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorSystemExistence` | 22 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralInverseSystemNormalization` | 22 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarRootAbelianTranspose` | 22 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarUnitAbelianTranspose` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportCore` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting` | 22 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackEndpoints` | 23 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainData` | 23 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatData` | 23 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedUnderivedData` | 23 | 1 | proof | route |
| `Sheaf.Paper.TowerRestrictedScalarAdjunction` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPull` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | 23 | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | 23 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCompositionLaw` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistFractionLaws` | 26 | 1 | proof | route |
| `Sheaf.SixFunctors.PullQuotientOrdinaryProjectionSection` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | 27 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | 29 | 1 | proof | route |
| `Sheaf.Paper.CanonicalIntegralEvaluationCalculus` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicTensorRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityNaturality` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionAugmentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralReductionTensorPullback` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralTensorReductionAugmentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 17 | 1 | proof | 1 |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | 18 | 4 | proof | 1 |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | - | 7 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.CondensedCompositorRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | - | 1 | proof | 1 |
| `Sheaf.Paper.SpecifiedHomScalarEvaluation` | - | 3 | proof | 1 |
| `Sheaf.Paper.PodReindexingTensorAugmentationSquare` | 18 | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | - | 9 | proof | 2 |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | - | 3 | proof | 2 |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | - | 6 | proof | 2 |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 12 | 7 | proof | 3 |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` | - | 1 | proof | 3 |

## Stage 3: waiting for statements of dependencies (10)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 6 | 1 | `lem-route-inverse-image-ring-functor` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | 9 | 1 | `lem-pod-rational-purity-pairing` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | 10 | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | 12 | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `Sheaf.Paper.IteratedPurityScalarPasting` | - | 2 | `lem-pur-rational-normalized-purity-diagrams` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 1 | `lem-pur-composition-comparison-scalar-compatibility` |
