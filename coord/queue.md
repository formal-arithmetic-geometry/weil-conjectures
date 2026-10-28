# Work queue

123 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (1 clusters, 685 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.SixFunctors.IntegralNormalizedFamily` | 1 |  | error: Sheaf/SixFunctors/IntegralNormalizedFamily.lean:161:61: Application type mismatch: The argument | hlimit | has type | ∃ a b c d e, | c.hom = diagonalDeri |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 2, stage 3 5 items.

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

## Stage 3: modules to prove (114)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.ConstantCompletionFiniteSystemProperties` | 10 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 11 | 1 | disputed | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward` | - | 1 | disputed | route |
| `Sheaf.Paper.FiniteModelCoefficientTransport` | - | 1 | disputed | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` | - | 1 | disputed | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization` | - | 1 | disputed | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateCanonical` | - | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 6 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 8 | 1 | proof | route |
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
| `Sheaf.Paper.CompletedPullbackTowerCore` | 12 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso` | 12 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives` | 12 | 1 | proof | route |
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
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistMultiplication` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistSectionRestriction` | - | 1 | proof | route |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | - | 3 | proof | route |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | - | 1 | proof | route |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | - | 1 | proof | route |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | - | 4 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | - | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | - | 3 | proof | route |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors` | - | 1 | proof | route |
| `Sheaf.Paper.FrobeniusIntegralRootTransport` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 11 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | - | 2 | proof | route |
| `Sheaf.Paper.IntegralRootPowerGenerators` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedKFlatFlat` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 20 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | - | 2 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarFiniteBoundaryComposition` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarP1UnitMateComponent` | - | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | - | 1 | proof | route |
| `Sheaf.Paper.StrictKummerPureKernelNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.SystemOperationExchangeRealization` | - | 7 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OrdinaryBasicSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 2 | proof | route |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalHomTransport` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness` | - | 1 | proof | route |
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
