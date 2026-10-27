# Work queue

167 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (3)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-pur-derived-pullback-tensor-constraints-common-associator-existence` | 6003 | none |
| `lem-pur-derived-pullback-tensor-constraints-common-braiding-existence` | 6003 | none |
| `lem-pur-derived-pullback-tensor-constraints-common-composition-existence` | 6003 | none |

## Stage 2: nodes to state (5)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-sf-native-proper-projection-realization` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |

Not open yet: 1135 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (158)

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
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 7 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 6 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | 6 | 1 | proof | route |
| `Sheaf.CategoryTheory.GeometricRingInverseImage` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.RestrictionTensorRepresentativeStageTransport` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsNormalization` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedInternalHomFibers` | 8 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionModels` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.ProperBaseChangeAdmissibleGenerators` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemModules` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionProjectionKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionQuotientKernel` | 10 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTensorModelNormalization` | 10 | 1 | proof | route |
| `Sheaf.WeilSheaf.CoefficientCohomologyComparison` | 10 | 1 | proof | route |
| `Sheaf.WeilSheaf.SmoothDualizingVanishing` | 10 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitBridge` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackStrictSquare` | 11 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 12 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap` | 12 | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | 13 | 2 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementComposition` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementIdentity` | 13 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence` | 13 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalLeft` | 13 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportInternalRight` | 13 | 1 | proof | route |
| `Sheaf.Paper.CoefficientPresentationIntegralMapIndependence` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparisonData` | 14 | 2 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` | 14 | 1 | proof | route |
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
| `Sheaf.Paper.AdicCommonPullbackIdentityUnit` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorFiniteModelCore` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicIntegralReindexingDescent` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensorCompatibility` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingUnitCompatibility` | 15 | 1 | proof | route |
| `Sheaf.Paper.AdicTensorReindexingModels` | 15 | 1 | proof | route |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA` | 15 | 9 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRationalCommonExactness` | 15 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.NativeProperScalarMateBoundedBelow` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 15 | 2 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTraceTransportCounit` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore` | 16 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence` | 16 | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChern` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjection` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionInterchange` | 16 | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | 16 | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | 16 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting` | 16 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarNormalizationExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.AmbientQuotientScalarRealizationExistence` | 17 | 1 | proof | route |
| `Sheaf.Paper.CanonicalSectionProjectionCore` | 17 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportTargetRationalComparison` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 2 | proof | route |
| `Sheaf.Paper.PodReindexingTensorLimitModel` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQLeftInverse` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernQRightInverse` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | 17 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison` | 17 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness` | 17 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | 18 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLaws` | 18 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingReductionTensorSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionData` | 18 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionShift` | 18 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinementFinite` | 18 | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` | 18 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare` | 18 | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | 18 | 3 | proof | route |
| `Sheaf.Paper.CanonicalIntegralEvaluationCalculus` | 19 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFinitePushUnit` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreData` | 19 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | 19 | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestrictionComponentIsIso` | 19 | 1 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | 19 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeRestrictionTensorEvaluation` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization` | 20 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateExtensionality` | 20 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported` | 21 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelNaturality` | 21 | 1 | proof | route |
| `Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension` | 21 | 1 | proof | route |
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
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | 27 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | 29 | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralReductionTensorPullback` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |

## Stage 3: waiting for statements of dependencies (7)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | 9 | 1 | `lem-pod-rational-purity-pairing` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | 10 | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | 12 | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
