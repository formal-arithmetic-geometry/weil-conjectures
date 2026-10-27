# Work queue

85 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (2 clusters, 1191 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.ConstructibleRingLeftRefinement` | 1 |  | error: Sheaf/Paper/ConstructibleRingLeftRefinement.lean:168:11: failed to synthesize | Mono ((R.left d (RingStage.integral L)).hom.app (SX.functor.obj K) ≫ Hd.m |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | 1 |  | error: Sheaf/Paper/TraceBoundedQuotientStalkRealization.lean:311:8: stuck at solving universe constraint | u + 1 =?= max (u + 1) ?u.37 | while trying to unify | |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 1, stage 3 1 items.

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

## Stage 3: modules to prove (76)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 11 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 12 | 1 | disputed | route |
| `Sheaf.Paper.FiniteModelCoefficientTransport` | 14 | 1 | disputed | route |
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
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 11 | 1 | proof | route |
| `Sheaf.Paper.RestrictionTensorRepresentativeStageTransport` | 11 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSectionsNormalization` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedInternalHomFibers` | 12 | 1 | proof | route |
| `Sheaf.Paper.CoefficientNormalizedReductionModels` | 12 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 12 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 14 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparisonData` | 14 | 2 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTensorModelNormalization` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackLimitBridge` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerPullbackStrictSquare` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CanonicalIntegralEvaluationCalculus` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicEvaluationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalCyclicUniformizerSquare` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerAdjunctTransport` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalUniformizerLocalChern` | - | 2 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteP1KummerBoundaryTransport` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComponent` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 12 | proof | route |
| `Sheaf.Paper.IntegralReductionTensorPullback` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralSupportAdjointOfPreservation` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedChainData` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.ProjectiveSupportedSourceNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.ProperBaseChangeAdmissibleGenerators` | - | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1ScalarChernBaseChangeChern` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SecondPullSection` | - | 1 | proof | route |
| `Sheaf.Paper.RationalP1SectionEvaluation` | - | 2 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | - | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | - | 1 | proof | route |
| `Sheaf.Paper.TensorReductionCanonicalSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 11 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.IntegralCompactSupportScalarTensor` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 2 | proof | 1 |

## Stage 3: waiting for statements of dependencies (6)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 9 | 6 | `lem-pur-rational-braiding-scalar-compatibility` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 10 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | - | 1 | `lem-sf-native-proper-projection-realization` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | - | 1 | `lem-pod-rational-purity-pairing` |
