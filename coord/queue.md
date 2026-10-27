# Work queue

213 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (5 clusters, 934 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | 1 |  | error: Sheaf/Paper/ExceptionalFiniteSupportRealization.lean:155:6: error: Application type mismatch: The argument | (integralExceptionalEtaleRealization l E X n |
| `Sheaf.Paper.NativeCompactSupportGeometry` | 1 |  | error: Sheaf/Paper/NativeCompactSupportGeometry.lean:42:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class | IsCommMonObj | ((sheaf |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | 1 |  | error: NOT ACCEPTED: compiled in 64.8 s > 60 s, the limit for one file (SHEAF_FILE_TIMEOUT). It ran up to 120 s only so that the slow declarations finish and re |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | 1 |  | error: Sheaf/Paper/ExceptionalDerivedSiteRealization.lean:250:10: error: synthesized type class instance is not definitionally equal to expression inferred by t |
| `Sheaf.Paper.TwistFrobeniusScalar` | 1 |  | error: NOT ACCEPTED: compiled in 82.6 s > 60 s, the limit for one file (SHEAF_FILE_TIMEOUT). It ran up to 120 s only so that the slow declarations finish and re |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 1, stage 3 3 items.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-pur-rational-tensor-associator-scalar-square` | 6004 | none |

## Stage 2: nodes to state (5)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |
| `lem-pur-integral-braiding-naturality` | 2 | state | 0 |
| `lem-pur-integral-braiding-scalar-extension-square` | 2 | state | 0 |
| `lem-pur-rational-braiding-scalar-compatibility` | 3 | state | 0 |

Not open yet: 1137 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up), 1 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (201)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 11 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 12 | 1 | disputed | route |
| `Sheaf.Paper.FiniteModelCoefficientTransport` | 14 | 1 | disputed | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative` | - | 1 | disputed | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting` | - | 1 | disputed | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | - | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.CategoryTheory.GeometricRingInverseImage` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 7 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 8 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport` | 9 | 1 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 9 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemModules` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionProjectionKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionQuotientKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageUnitCoherence` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralCompositionCoherence` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitCoherence` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorRationalCompositionCoherence` | 10 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorRationalUnitCoherence` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 11 | 1 | proof | route |
| `Sheaf.Paper.RestrictionTensorRepresentativeStageTransport` | 11 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientPullbackIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackCompositionLaws` | 12 | 1 | proof | route |
| `Sheaf.Paper.AmbientTensorComposition` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsNormalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransport` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemHomProjectionTransport` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedInternalHomFibers` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionModels` | 12 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 12 | 2 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives` | 12 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare` | 12 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorChainComposition` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality` | 14 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparisonData` | 14 | 2 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.OrdinaryQuotientScalarTowerComparison` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTensorModelNormalization` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackStrictSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport` | 15 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualLevelDescent` | 16 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicScalarModel` | 16 | 1 | proof | route |
| `Sheaf.Paper.EtaleNormalizationArrowUniversal` | 17 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicLiftedTransitionUniversal` | 17 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelRealizationExtensionIso` | 19 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIso` | 19 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModel` | 19 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleStalks` | 19 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap` | 19 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedRealization` | 19 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerScalarRestriction` | 19 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralCoproductAdjunction` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistIdentity` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistMultiplication` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistUniqueness` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistUnit` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal` | - | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | - | 2 | proof | route |
| `Sheaf.Paper.AdicCommonPullbackIdentityUnit` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorFiniteModelCore` | - | 1 | proof | route |
| `Sheaf.Paper.AdicIntegralReindexingDescent` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingUnitCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.AdicTensorReindexingModels` | - | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarNormalizationExistence` | - | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarRealizationExistence` | - | 1 | proof | route |
| `Sheaf.Paper.CanonicalIntegralEvaluationCalculus` | - | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionCore` | - | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionTransport` | - | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported` | - | 1 | proof | route |
| `Sheaf.Paper.CoefNativeRestrictionTensorEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalComparison` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFinitePushUnit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | - | 2 | proof | route |
| `Sheaf.Paper.ExceptionalRationalCommonExactness` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreData` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLaws` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | - | 2 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicTensorComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackChainSquare` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 12 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementComposition` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementIdentity` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionAugmentationDescent` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionAugmentationGood` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralReductionTensorPullback` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpoint` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackUnitsEndpoint` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelNaturality` | - | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainData` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatFlat` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.ProperBaseChangeAdmissibleGenerators` | - | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportExtension` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlat` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalLeft` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalRight` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportIso` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCounit` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChern` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQLeftInverse` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQRightInverse` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjection` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchange` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | - | 2 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarP1UnitMateComponent` | - | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | - | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralAbelianComparison` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralUnitNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.TowerScalarRootAbelianTransposeComponent` | - | 1 | proof | route |
| `Sheaf.Paper.TowerScalarUnitAbelianTransposeSection` | - | 1 | proof | route |
| `Sheaf.Paper.VectorIntegrationPresentationIso` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPullComplex` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonAssembly` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryBasicSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryProperOpenInvertibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | - | 1 | proof | route |
| `Sheaf.TraceFormula.CanonicalRelativeProjProper` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 11 | 2 | proof | 1 |
| `Sheaf.CategoryTheory.ScalarHomZeroCompatibility` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 2 | proof | 1 |

## Stage 3: waiting for statements of dependencies (7)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 9 | 6 | `lem-pur-rational-braiding-scalar-compatibility` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 10 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | - | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | - | 1 | `lem-pod-rational-purity-pairing` |
