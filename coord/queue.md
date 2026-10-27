# Work queue

210 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (2 clusters, 625 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `WeilConjectures.TraceFormula.CompactCohomology` | 1 |  | error: NOT ACCEPTED: compiled in 93.2 s > 60 s, the limit for one file (SHEAF_FILE_TIMEOUT). It ran up to 120 s only so that the slow declarations finish and re |
| `Sheaf.Paper.TowerOrientationEvaluation` | 1 |  | error: Sheaf/Paper/TowerOrientationEvaluation.lean:131:14: error(lean.synthInstanceFailed): failed to synthesize instance of type class | (SpTowerP1.realization |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 0 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (8)

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

Not open yet: 1135 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (199)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 4 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 8 | 1 | disputed | route |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | 14 | 1 | disputed | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 15 | 1 | disputed | route |
| `Sheaf.Paper.EtaleCofinalSupportComposition` | 19 | 1 | disputed | route |
| `Sheaf.Paper.EtaleScalarPullbackTensorCoherence` | 3 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 7 | proof | route |
| `Sheaf.Paper.StrictTateTensorTowerLift` | 4 | 1 | proof | route |
| `Sheaf.Paper.TateTensorNormalizedSquare` | 4 | 1 | proof | route |
| `Sheaf.Paper.TateTensorQuotientBalancing` | 4 | 1 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 6 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCompositionCoherence` | 5 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorUnitCoherence` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionIntegratedSpecializationIntegrationBaseChange` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionIntegratedSpecializationSpecializationBaseChange` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothOrdinaryTwistCocycle` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothPuritySourceCocycle` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | 6 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemResolutionModels` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPull` | 7 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.ReductionExceptionalChart` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.Paper.DiagonalOrdinaryReesNormalization` | 8 | 1 | proof | route |
| `Sheaf.Paper.EtaleOrderedOpenProjectionScalar` | 8 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.FiniteSectionSpecializationScalarCanonical` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTowerComponent` | 9 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 2 | proof | route |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceExponent` | 9 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelContractions` | 9 | 1 | proof | route |
| `Sheaf.Paper.OpenScalarCounitSquare` | 10 | 4 | proof | route |
| `Sheaf.Paper.RationalP1UnitCounit` | 10 | 3 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExact` | 10 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralKernelUnitCounit` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose` | 11 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionDerivedComparisonExistence` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportExtension` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportKFlat` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedBarB` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedPure` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalizedTotal` | 11 | 1 | proof | route |
| `Sheaf.Paper.TraceBaseChangeSecond` | 11 | 1 | proof | route |
| `Sheaf.Paper.VectorTraceScalarDescent` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 2 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 15 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | 12 | 1 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 12 | 7 | proof | route |
| `Sheaf.Paper.DiagonalQuotientClassPullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalQuotientSourcePullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalQuotientTracePullback` | 13 | 1 | proof | route |
| `Sheaf.Paper.DiagonalScalarPullbackCompatibility` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteClopenCommonExceptional` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteTateScalarSourceExistence` | 13 | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityScalarCompatibility` | 13 | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityScalarLineWitness` | 13 | 1 | proof | route |
| `Sheaf.Paper.P1KummerChernScalar` | 13 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransport` | 13 | 1 | proof | route |
| `Sheaf.Paper.RationalP1UnitFactorization` | 13 | 1 | proof | route |
| `Sheaf.Paper.SmoothClopenComponentInverse` | 13 | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransport` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedClassPullback` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedTracePullback` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerScalarSquares` | 14 | 1 | proof | route |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | 14 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | 14 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | 14 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSectionProjection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 1 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | 14 | 1 | proof | route |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | 14 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransport` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChange` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernSplittings` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPretrace` | 15 | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | 15 | 1 | proof | route |
| `Sheaf.Paper.StrictKummerUnitNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.SystemOpenScalarEvaluation` | 15 | 1 | proof | route |
| `Sheaf.Paper.SystemProperScalarEvaluation` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenFlatDetection` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralData` | 16 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarModelExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalEvaluationUnit` | 16 | 1 | proof | route |
| `Sheaf.Paper.EtaleQuotientTensorProjection` | 16 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 16 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitSquare` | 16 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquare` | 16 | 1 | proof | route |
| `Sheaf.Paper.SfDirectImageRestrictionPasting` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownOpenSingletonEvaluation` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingOperationsExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCore` | 17 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinement` | 17 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapOpenUnit` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownImageRealization` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownLevelRealization` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownOpenScalarTransport` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleBrownProperScalarTransport` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleSystemProjectionBasicData` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleSystemProjectionComparisonData` | 18 | 1 | proof | route |
| `Sheaf.Paper.EtaleSystemRestrictionEvaluation` | 18 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarFiniteBoundary` | 18 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalFiniteScalar` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalFiniteScalarMaps` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalFiniteScalarOperation` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | 19 | 1 | proof | route |
| `Sheaf.Paper.EtaleCofinalExtensionExistence` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalProScalarActions` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalProperOpenOriginConstruction` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalProperOpenOriginProperties` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalSiteOriginComparisonCore` | 20 | 3 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluationComponent` | 21 | 1 | proof | route |
| `Sheaf.Paper.EtaleCofinalBlockFactorization` | 21 | 1 | proof | route |
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
| `Sheaf.Paper.TowerRestrictedScalarAdjunction` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPull` | 23 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | 23 | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | 23 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenLambdaCompletionIso` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport` | 24 | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCompositionLaw` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistFractionLaws` | 26 | 1 | proof | route |
| `Sheaf.Paper.BasicOperationCoefficientCoherence` | 26 | 1 | proof | route |
| `Sheaf.SixFunctors.PullQuotientOrdinaryProjectionSection` | 26 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | 27 | 1 | proof | route |
| `Sheaf.Paper.CoefficientTensorNormalization` | 27 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportNormalizedReductionTower` | 27 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientHomModelComparison` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | 29 | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.TwistedActionUnderivedRestriction` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCore` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingFunctoriality` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.CondensedCompositorRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingTensorAugmentationSquare` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (8)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 6 | 1 | `lem-route-inverse-image-ring-functor` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | - | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | - | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | - | 1 | `lem-pod-rational-purity-pairing` |
