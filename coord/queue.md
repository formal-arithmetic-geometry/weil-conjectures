# Work queue

263 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (1 clusters, 169 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.AdicCompletedTensorComponentStageTransport` | 1 |  | error: Sheaf/Paper/AdicCompletedTensorComponentStageTransport.lean:77:16: (kernel) deterministic timeout | error: Sheaf/Paper/AdicCompletedTensorComponentStageT |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 3 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (11)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 1 |
| `lem-sp-ctf-tower-pullback-reconstruction` | 1 | state | 1 |
| `lem-a1-completed-scalar-exact-base-change` | 1 | state | 0 |
| `lem-a1-projective-quotient-augmentation` | 1 | state | 0 |
| `lem-per-continuous-filtration-admissible-strata` | 1 | state | 0 |
| `lem-per-integral-piece-completion-normalization` | 1 | state | 0 |
| `lem-pur-general-legacy-common-stage-cones` | 1 | state | 0 |
| `lem-pur-tower-purity-ground-field-retagging` | 1 | state | 0 |
| `lem-coef-ramified-scalar-counit-limit` | 2 | state | 0 |
| `lem-pur-composition-comparison-scalar-compatibility` | 2 | state | 0 |
| `lem-pur-rational-normalized-purity-diagrams` | 2 | state | 0 |

Not open yet: 1131 nodes that below a finished node, not needed, 1 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (250)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `WeilConjectures.SmoothPurity.Defs` | 0 | 2 | disputed | route |
| `Sheaf.SmoothPurity.TraceExistence` | 1 | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 8 | 1 | disputed | route |
| `Sheaf.Paper.IntegralCompactSupportRestrictionShift` | 13 | 1 | disputed | route |
| `Sheaf.Paper.RingEndpointScalarIdentityNormalization` | 17 | 1 | disputed | route |
| `Sheaf.Paper.FinitePerfectAdicCoordinateTransitionCoherence` | 18 | 1 | disputed | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization` | 19 | 1 | disputed | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps` | 21 | 1 | disputed | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatResolution` | - | 1 | disputed | route |
| `Sheaf.Paper.PodReindexingReductionTensorSquareDescent` | - | 1 | disputed | route |
| `Sheaf.Paper.FiniteProperComparisonIso` | 13 | 1 | disputed | 1 |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | - | 1 | disputed | 3 |
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 6 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 5 | 5 | proof | route |
| `Sheaf.Paper.FiniteTateRootTensorPresentation` | 5 | 1 | proof | route |
| `Sheaf.Paper.CommonStagePullbackCompComponent` | 6 | 2 | proof | route |
| `Sheaf.Paper.CompletedComparisonCanonicalIdentification` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackTensorCompositionReduced` | 7 | 1 | proof | route |
| `Sheaf.Paper.PbcScalarTensor` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenCounitFiniteSupportDiagram` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperQcOpenCounitSections` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 8 | 2 | proof | route |
| `Sheaf.Paper.CompletedScalarBetaComparison` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompletedScalarRouteCoordinates` | 8 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.OrdinaryChartExceptionalScalar` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenBoundaryTestHypercohomology` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsCoreEquations` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsScalarHomZeroRepresentative` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientFiniteQuotientCalculusExistence` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionModelExistence` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorAssociativityHom` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantKoszulCoefficientConeComparison` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantKoszulQuotientAugmentation` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantKoszulTensorConeComparison` | 10 | 1 | proof | route |
| `Sheaf.Paper.SpecifiedHomScalarRationalNaturality` | 10 | 1 | proof | route |
| `Sheaf.Paper.SpecifiedHomScalarTower` | 10 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedTensorHorizontalRepresentative` | 11 | 1 | proof | route |
| `Sheaf.Paper.CoefficientStrictReductionTensorComparison` | 11 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 12 | 8 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 12 | 5 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactShiftCore` | 12 | 1 | proof | route |
| `Sheaf.Paper.AffineSpacePolynomialDeformation` | 13 | 1 | proof | route |
| `Sheaf.Paper.ScalarCompletionQuotientPresentation` | 13 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport` | 13 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftComponent` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementCompositionAfterInclusion` | 14 | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 14 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | 14 | 1 | proof | route |
| `Sheaf.Paper.ConstructiblePullbackTExact` | 15 | 2 | proof | route |
| `Sheaf.Paper.DiagonalAdicEvaluationComparison` | 15 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCompletedReductionRestriction` | 15 | 1 | proof | route |
| `Sheaf.Paper.DiagonalSupportedOrdinaryLimit` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteRingOpenRestrictionCoordinates` | 15 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerConstantComplexComparisons` | 15 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizedConstantsModel` | 15 | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSectionTransportData` | 15 | 1 | proof | route |
| `Sheaf.Paper.SystemDirectImageReductionNormalized` | 15 | 1 | proof | route |
| `Sheaf.Paper.SystemDirectImageRestrictedTowerComparison` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompCompForgetSupports` | 16 | 1 | proof | route |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | 16 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientRealizationIsoHomLift` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | 16 | 1 | proof | route |
| `Sheaf.Paper.FdRawScalarComparisonPackaging` | 16 | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportOperationRealization` | 16 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoDescent` | 16 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerLocalizationComparisons` | 16 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSectionCoreConjugate` | 16 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosCounitNormalization` | 16 | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | 17 | 3 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | 17 | 2 | proof | route |
| `Sheaf.Paper.ExceptionalRationalNormalizedScalarShift` | 17 | 1 | proof | route |
| `Sheaf.Paper.FdIntegralScalarPresentationForward` | 17 | 1 | proof | route |
| `Sheaf.Paper.FdIntegralScalarRestrictionExact` | 17 | 1 | proof | route |
| `Sheaf.Paper.FdRawLocalizationScalarDescent` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstScalarTrace` | 17 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondExchangeProjectionNative` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleProperCompositorGraphTranspose` | 18 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleProperSheafUnitGraphTranspose` | 18 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralReductionLeftCompatibility` | 18 | 1 | proof | route |
| `Sheaf.Paper.FdCoefficientScalarLiftNormalization` | 18 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerKernelConstantComparison` | 18 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerOrdinaryTensorComparison` | 18 | 1 | proof | route |
| `Sheaf.Paper.IntegralComparisonPullbackRealizationShifts` | 18 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveDiagramSingle` | 18 | 1 | proof | route |
| `Sheaf.Paper.ProjectiveResidualTarget` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalP1FirstTracePretrace` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ProjectionScalarEvaluation` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernSomeRaw` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondProjectionTailCore` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalRestrictionPullbackUnit` | 18 | 1 | proof | route |
| `Sheaf.Paper.RationalScalarExtensionRightAdjoint` | 18 | 1 | proof | route |
| `Sheaf.Paper.ScalarComponentFromTrace` | 18 | 1 | proof | route |
| `Sheaf.Paper.ShiftedLineSquare` | 18 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerTarget` | 19 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarComponents` | 19 | 1 | proof | route |
| `Sheaf.Paper.RationalP1ClosureExchangeNaturality` | 19 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreEvaluationCounit` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreEvaluationSupport` | 20 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreEvaluationUnit` | 20 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaPullbackKFlat` | 20 | 1 | proof | route |
| `Sheaf.Paper.FiniteIntegralCoefficientComparison` | 20 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackStrictTowerComparison` | 20 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackRoosFiniteTower` | 20 | 1 | proof | route |
| `Sheaf.Paper.StrictIntegralCoefficientTowerTransport` | 20 | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSourceEquation` | 21 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceSupportedFiniteBoundarySource` | 21 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryTarget` | 21 | 1 | proof | route |
| `Sheaf.Paper.FiniteP1OrdinaryKummerBoundaryCore` | 21 | 1 | proof | route |
| `Sheaf.Paper.DiagonalFiniteConstantAdjunct` | 22 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceShiftedRootProjectionTransportCore` | 22 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralRightReduction` | 22 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportObjects` | 22 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalTransportLeftShift` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingBaseChange` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjTwistQuasicoherent` | 28 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | 28 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemClopenTailBridge` | 28 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemIntrinsicLambdaExpansion` | 28 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenPrefixBridge` | 28 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime` | 29 | 1 | proof | route |
| `Sheaf.Paper.FiniteHomIntrinsicTensorComposition` | 29 | 1 | proof | route |
| `Sheaf.Paper.FiniteHomSiteTensorCoherence` | 30 | 1 | proof | route |
| `Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap` | 32 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionNormalizationData` | 32 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReductionTowerUnitModels` | 32 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomScalarEvaluationInvertible` | 33 | 1 | proof | route |
| `Sheaf.Paper.PerfectCoefficientSignedHomAction` | 33 | 1 | proof | route |
| `Sheaf.Paper.ReductionTensorResolutionComparison` | 33 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueGeometricCompatibility` | 34 | 1 | proof | route |
| `Sheaf.CategoryTheory.NativeHomLocalizedConeBoundaryModel` | 36 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedSiteGlobalRHomCoefficientModel` | - | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedSiteGlobalRHomResolvedTowerModels` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedRightAction` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedRightPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare` | - | 1 | proof | route |
| `Sheaf.Paper.AdicFiniteConstructibilityComparison` | - | 1 | proof | route |
| `Sheaf.Paper.AdicFiniteScalarCoherence` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexBalancedScalar` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexScalarSource` | - | 1 | proof | route |
| `Sheaf.Paper.AdicSmoothDualizingFiniteComparison` | - | 2 | proof | route |
| `Sheaf.Paper.AdicSmoothDualizingFinitePowers` | - | 1 | proof | route |
| `Sheaf.Paper.CoefDualizingClosedChart` | - | 1 | proof | route |
| `Sheaf.Paper.CoefficientSequenceEvaluationFull` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CondensedFiniteIntegralTensorModel` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionOpenFactor` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionProperFactor` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionDiamondRightCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackCompositionFixedCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackOrdinarySquare` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralConstantUnitFrobenius` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralHomComparisonUncurry` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicCondensedIntegralNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicFiniteCocone` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGeneratorIntegral` | - | 1 | proof | route |
| `Sheaf.Paper.NativeIntegralCoefficientFlat` | - | 1 | proof | route |
| `Sheaf.Paper.NativeOpenTensorRestrictionForget` | - | 1 | proof | route |
| `Sheaf.Paper.NativeScalarRestrictionCube` | - | 1 | proof | route |
| `Sheaf.Paper.NativeScalarRingModel` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedAssociatorRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedUnitSymmetryRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.PodIdentityTensorTower` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingCompositionTensor` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedFiniteModel` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedLimitModel` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedLimitProjection` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedReductionEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingDerivedUnit` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 17 | proof | route |
| `Sheaf.Paper.PodReindexingHomResolutionModel` | - | 2 | proof | route |
| `Sheaf.Paper.PodReindexingTensorLimitModelDescent` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingTensorSignedShiftCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.PodTensorFiniteShiftTransitions` | - | 1 | proof | route |
| `Sheaf.Paper.PodTensorRoosRepresentativeSquare` | - | 1 | proof | route |
| `Sheaf.Paper.PodTensorShiftRoosPathNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.PodTensorSignedShiftDescent` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeLeftPrefix` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | proof | route |
| `Sheaf.Paper.RationalHomScalarTranspose` | - | 1 | proof | route |
| `Sheaf.Paper.RationalModuleLocalModelsTransport` | - | 1 | proof | route |
| `Sheaf.Paper.RationalModuleLocalizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.RationalProperProjectionInvertible` | - | 1 | proof | route |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | - | 5 | proof | route |
| `Sheaf.Paper.RationalStratumIntegralModels` | - | 2 | proof | route |
| `Sheaf.Paper.RationalTensorSymmetry` | - | 1 | proof | route |
| `Sheaf.Paper.StratifiedPerfectInternalHomCoproducts` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateRhsCoreFiniteMate` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CartesianCandidateSiteSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CartesianTowerRestriction` | - | 1 | proof | route |
| `Sheaf.SixFunctors.ClosedOpenDualizingMateNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | - | 3 | proof | route |
| `Sheaf.SixFunctors.CoefHomScalarNaturality` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionPureTensor` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionTranspose` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionUnitReduction` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefPairingCompactificationModels` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefPairingNativeOperations` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarDualFormulaInclusionScalar` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierFiniteTower` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierFiniteUnit` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierShiftComponents` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | - | 3 | proof | route |
| `Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryResolving` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualFormulaComparison` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingFiniteCounitCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralDualizingSystemFiniteEvaluation` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralHomScalarTensorRepresentativeComparison` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarComparisonCanonicalTransition` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PointIntegralReductionHomTower` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.SixFunctors.RationalDualFormulaScalarCounit` | - | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierDatumNaturality` | - | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierTensorRoosSignedModel` | - | 1 | proof | route |
| `Sheaf.SixFunctors.RationalVerdierTensorTowerSignedCoordinate` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.FourierInversion.AffineChartLocalization` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.FourierInversion.ProjectiveLineDecomposition` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalCompactSupportIntegralTransition` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.RealizedTateCohomology` | - | 1 | proof | route |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | 13 | 2 | proof | 1 |
| `Sheaf.Paper.IntegralProperOpenDerivedLimit` | 13 | 1 | proof | 1 |
| `Sheaf.Paper.DiagonalCompletedTracePullback` | 14 | 1 | proof | 1 |
| `Sheaf.SixFunctors.EtaleScalarTensorShiftCancellation` | 14 | 1 | proof | 1 |
| `Sheaf.Paper.PointRealizationStandardCohomology` | 16 | 2 | proof | 1 |
| `Sheaf.Paper.AdicClosedConstructible` | - | 9 | proof | 1 |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 1 | proof | 1 |
| `Sheaf.Paper.ContinuousScalarEncodingUniverses` | - | 1 | proof | 1 |
| `Sheaf.Paper.FdIntegralInverseScalarCocycle` | - | 2 | proof | 1 |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 3 | proof | 1 |
| `Sheaf.SixFunctors.CoefHomTowerScalarModel` | - | 6 | proof | 1 |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.FiniteCounitRestrictionSquare` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.FinitePointTransportUnit` | 14 | 1 | proof | 2 |
| `Sheaf.Paper.FinitePullbackUnitComposition` | 14 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteClosedShriek` | - | 5 | proof | 2 |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.CoefficientProjectionPointData` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteClosedShriekMapPart` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | - | 2 | proof | 3 |
| `Sheaf.Paper.IteratedPurityScalarPasting` | - | 1 | proof | 4 |

## Stage 3: waiting for statements of dependencies (6)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-common-stage-cones` |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | - | 2 | `lem-a1-projective-quotient-augmentation` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | - | 4 | `lem-pur-tower-purity-ground-field-retagging` |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | - | 1 | `lem-sp-ctf-tower-pullback-reconstruction` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 1 | `lem-pur-composition-comparison-scalar-compatibility` |
