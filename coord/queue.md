# Work queue

88 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (3 clusters, 625 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | 1 |  | error: failed in the global build 2026-10-27T17:42:16Z with this text (coord/build-errors/Sheaf.Paper.CoefficientTowerShriekInterfaces.txt) |
| `Sheaf.Paper.TowerClassPositiveUnitSquare` | 1 |  | error: Sheaf/Paper/TowerClassPositiveUnitSquare.lean:212:4: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached | Note: Us |
| `Sheaf.Paper.IntegralDirectImageTowerData` | 1 |  | error: failed in the global build 2026-10-27T17:42:16Z with this text (coord/build-errors/Sheaf.Paper.IntegralDirectImageTowerData.txt) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 0 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (5)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-sf-native-ordinary-chain-currying` | 1 | state | 0 |
| `lem-sf-native-ordinary-model-uniqueness` | 1 | state | 0 |
| `lem-sf-native-proper-projection-realization` | 1 | state | 0 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |

Not open yet: 1135 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (79)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 12 | 1 | disputed | route |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | - | 1 | disputed | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 7 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 8 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryReducedPull` | 8 | 1 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | 9 | 6 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 9 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorCompositionCoherence` | 9 | 1 | proof | route |
| `Sheaf.Paper.PullbackTensorUnitCoherence` | 9 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorConstruction` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 11 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 11 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas` | 11 | 1 | proof | route |
| `Sheaf.Paper.CoefficientDerivedSystemResolutionModels` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 12 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTowerComponent` | 13 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 14 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenFlatDetection` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralData` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.TwistedActionUnderivedRestriction` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCore` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingFunctoriality` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 15 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | - | 2 | proof | route |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | - | 1 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | - | 1 | proof | route |
| `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` | - | 1 | proof | route |
| `Sheaf.Paper.SfDirectImageRestrictionPasting` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.TowerScalarFiniteBoundary` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPull` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 11 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 3 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 1 | proof | 1 |
| `Sheaf.Paper.ScalarTowerPullbackLimitSquare` | - | 1 | proof | 1 |
| `Sheaf.Paper.ScalarTowerTensorLimitSquare` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingTensorAugmentationSquare` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (7)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 10 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
| `Sheaf.Paper.NativeCompactProjectionFormula` | - | 1 | `lem-sf-native-proper-projection-realization` |
| `Sheaf.Paper.ProjectionFormulaCoherence` | - | 6 | `lem-sf-projection-base-change-common` |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | - | 1 | `lem-sf-native-ordinary-model-uniqueness` |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | - | 1 | `lem-pod-rational-purity-pairing` |
