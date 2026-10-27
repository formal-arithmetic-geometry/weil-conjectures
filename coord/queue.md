# Work queue

329 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (1 clusters, 485 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.NativeWeilScalarCounitData` | 1 |  | error: NOT ACCEPTED: compiled in 84.6 s > 60 s, the limit for one file (SHEAF_FILE_TIMEOUT). It ran up to 120 s only so that the slow declarations finish and re |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 3 items.

## Stage 1: nodes to split (5)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-route-twist-scalar-maps-exists-unique` | 2006 | none |
| `lem-pur-integral-scalar-reduction-intertwining` | 6005 | none |
| `lem-pur-integral-tensor-associator-naturality` | 6005 | none |
| `lem-pur-system-scalar-associator-coherence` | 6005 | none |
| `lem-route-twist-line-scalar-iso-exists-unique` | 6007 | none |

## Stage 2: nodes to state (13)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-sp-ctf-tower-pullback-reconstruction` | 1 | state | 1 |
| `lem-pur-tower-purity-ground-field-retagging` | 1 | state | 0 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-sf-native-proper-projection-realization` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |
| `lem-pur-composition-comparison-scalar-compatibility` | 2 | state | 0 |
| `lem-pur-integral-braiding-naturality` | 2 | state | 0 |
| `lem-pur-integral-braiding-scalar-extension-square` | 2 | state | 0 |
| `lem-pur-rational-normalized-purity-diagrams` | 2 | state | 0 |
| `lem-pur-rational-tensor-associator-scalar-square` | 2 | state | 0 |
| `lem-pur-rational-braiding-scalar-compatibility` | 3 | state | 0 |

Not open yet: 1130 nodes that below a finished node, not needed, 3 nodes that wait for a statement dependency (bottom-up), 3 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (309)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 3 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 7 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 8 | 1 | disputed | route |
| `Sheaf.Paper.FiniteModelCoefficientTransport` | 14 | 1 | disputed | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting` | 17 | 1 | disputed | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative` | 20 | 1 | disputed | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | 21 | 1 | disputed | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | - | 1 | disputed | 2 |
| `Sheaf.SmoothPurity.TraceExistence` | 1 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 7 | proof | route |
| `Sheaf.Paper.CoefficientTwistsDetailed` | 5 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.StrictTateTensorTowerLiftData` | 5 | 1 | proof | route |
| `Sheaf.Paper.StrictTateTensorTowerLiftEvaluation` | 5 | 1 | proof | route |
| `Sheaf.Paper.TateTensorGeneratorIsIso` | 5 | 1 | proof | route |
| `Sheaf.Paper.TateTensorNormalizedSquarePair` | 5 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCommonStageUnitCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralCompositionCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorIntegralUnitCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorRationalCompositionCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorRationalUnitCoherence` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | 6 | 1 | proof | route |
| `Sheaf.Paper.TateTensorGeneratorMap` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic` | 7 | 1 | proof | route |
| `Sheaf.CategoryTheory.GeometricRingInverseImage` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.RestrictionTensorRepresentativeStageTransport` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology` | 8 | 1 | proof | route |
| `Sheaf.Paper.AmbientCoefficientPullbackIso` | 8 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackCompositionLaws` | 8 | 1 | proof | route |
| `Sheaf.Paper.AmbientTensorComposition` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsNormalization` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransport` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemHomProjectionTransport` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedInternalHomFibers` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionModels` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport` | 8 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives` | 8 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorChainComposition` | 9 | 1 | proof | route |
| `Sheaf.Paper.ProperBaseChangeAdmissibleGenerators` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 1 | proof | route |
| `Sheaf.Paper.VectorIntegrationPresentationIso` | 9 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemModules` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionProjectionKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionQuotientKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.OrdinaryQuotientScalarTowerComparison` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportExtension` | 10 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTensorModelNormalization` | 10 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExact` | 10 | 1 | proof | route |
| `Sheaf.WeilSheaf.SmoothDualizingVanishing` | 10 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | 11 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransportKFlat` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitBridge` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackStrictSquare` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | 12 | 1 | proof | route |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 12 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap` | 12 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | 12 | 6 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 12 | 7 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | 13 | 2 | proof | route |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | 13 | 7 | proof | route |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | 13 | 3 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelRealizationExtensionIso` | 13 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIso` | 13 | 1 | proof | route |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | 13 | 4 | proof | route |
| `Sheaf.Paper.FrobeniusCompactIntegralNormalization` | 13 | 1 | proof | route |
| `Sheaf.Paper.FrobeniusIntegralRootTransport` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementComposition` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementIdentity` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralRootPowerGenerators` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleModel` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelEtaleStalks` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedRealization` | 13 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerScalarRestriction` | 13 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence` | 13 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalLeft` | 13 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalRight` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientPresentationIntegralMapIndependence` | 14 | 1 | proof | route |
| `Sheaf.Paper.CommonStagePullbackCompNaturality` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparisonData` | 14 | 2 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonIsIso` | 14 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomEvaluationNaturality` | 14 | 1 | proof | route |
| `Sheaf.Paper.NativeCompletedCoefficientChangeData` | 14 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | 14 | 21 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 2 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalHomScalarEvaluation` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierComparisonBiduality` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierComparisonEvaluation` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierComparisonNaturality` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierCompositionEquation` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierCompositionNormalization` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierDatumFromIntegral` | 14 | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierDatumNaturality` | 14 | 1 | proof | route |
| `Sheaf.CategoryTheory.ExactDerivedHomComparisonShift` | 15 | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeDerivedHomSignedExact` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicCommonPullbackIdentityUnit` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorFiniteModelCore` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicIntegralReindexingDescent` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingComposition` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingIdentity` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensorCompatibility` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingUnitCompatibility` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicTensorReindexingModels` | 15 | 1 | proof | route |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | 15 | 2 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA` | 15 | 9 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRationalCommonExactness` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomModelsExist` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeProperScalarMateBoundedBelow` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCounit` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionComposition` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityE` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityL` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionUInvertibility` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingAffineRestriction` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteIntrinsicBidualComparison` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimitHom` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta` | 15 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence` | 16 | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | 16 | 2 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualLevelDescent` | 16 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicScalarModel` | 16 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerComponents` | 16 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChern` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjection` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchange` | 16 | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | 16 | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionComp` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparison` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralCoproductAdjunction` | 17 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarNormalizationExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarRealizationExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionCore` | 17 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalComparison` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 2 | proof | route |
| `Sheaf.Paper.EtaleNormalizationArrowUniversal` | 17 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 2 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicLiftedTransitionUniversal` | 17 | 1 | proof | route |
| `Sheaf.Paper.IntrinsicSiteHomTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedComparisons` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingEvaluatedComparison` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingSignedShifts` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorCoefficientTransition` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorConstruction` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorFamilyCoherence` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorLimitModel` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedShifts` | 17 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSubstitution` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQLeftInverse` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQRightInverse` | 17 | 1 | proof | route |
| `Sheaf.Paper.ScalarP1UnitMateComponent` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | 18 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLaws` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingReductionTensorSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionData` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionShift` | 18 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinementFinite` | 18 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData` | 18 | 1 | proof | route |
| `Sheaf.Paper.CanonicalIntegralEvaluationCalculus` | 19 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFinitePushUnit` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreData` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | 19 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionComponentIsIso` | 19 | 1 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPullComplex` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonAssembly` | 19 | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryBasicSquare` | 19 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeRestrictionTensorEvaluation` | 20 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality` | 20 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported` | 21 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarCompletedModel` | 21 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelNaturality` | 21 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension` | 21 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteCore` | 22 | 1 | proof | route |
| `Sheaf.Paper.IsomorphismScalarFiniteSquares` | 22 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | 22 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainData` | 23 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralAbelianComparison` | 23 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralUnitNormalization` | 23 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarRootAbelianTransposeComponent` | 23 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarUnitAbelianTransposeSection` | 23 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackIntegerEndpoint` | 24 | 1 | proof | route |
| `Sheaf.Paper.IntegralSitePullbackUnitsEndpoint` | 24 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatFlat` | 24 | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatLocalization` | 24 | 1 | proof | route |
| `Sheaf.TraceFormula.CanonicalRelativeProjProper` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistIdentity` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistMultiplication` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistUniqueness` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistUnit` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | 29 | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicTensorComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackChainSquare` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionAugmentationDescent` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionAugmentationGood` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralReductionTensorPullback` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryProperOpenInvertibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.IntegralAutomorphismCancellationNormalization` | 14 | 1 | proof | 1 |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | 14 | 3 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 15 | 2 | proof | 1 |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | 18 | 3 | proof | 1 |
| `Sheaf.Paper.FiniteHomDomainCalculus` | 22 | 2 | proof | 1 |
| `Sheaf.CategoryTheory.ScalarHomZeroCompatibility` | - | 1 | proof | 1 |
| `Sheaf.Paper.CoefDualizingClosedChart` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.CoefficientDualizingClosedDescent` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | 15 | 6 | proof | 2 |
| `Sheaf.Paper.FiniteClosedShriek` | - | 6 | proof | 2 |
| `Sheaf.Paper.PointSystemTransportDescent` | - | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarAdjunctionCounit` | - | 1 | proof | 3 |
| `Sheaf.Paper.DirectImageReductionHomSquare` | - | 10 | proof | 4 |

## Stage 3: waiting for statements of dependencies (13)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 6 | `lem-pur-rational-braiding-scalar-compatibility` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | 9 | 1 | `lem-pod-rational-purity-pairing` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | 10 | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | 12 | 4 | `lem-pur-tower-purity-ground-field-retagging` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | 12 | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `Sheaf.Paper.IteratedPurityScalarPasting` | - | 2 | `lem-pur-rational-normalized-purity-diagrams` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 1 | `lem-pur-composition-comparison-scalar-compatibility` |
