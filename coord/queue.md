# Work queue

178 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (3 clusters, 3737 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | 1 |  | error: failed in the global build 2026-10-27T17:42:16Z with this text (coord/build-errors/Sheaf.Paper.CoefficientTowerShriekInterfaces.txt) |
| `Sheaf.Paper.TowerClassPositiveUnitSquare` | 1 |  | error: Sheaf/Paper/TowerClassPositiveUnitSquare.lean:212:4: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached | Note: Us |
| `Sheaf.Paper.IntegralDirectImageTowerData` | 1 |  | error: failed in the global build 2026-10-27T17:42:16Z with this text (coord/build-errors/Sheaf.Paper.IntegralDirectImageTowerData.txt) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 1 items.

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

## Stage 3: modules to prove (169)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization` | - | 1 | disputed | route |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | - | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 10 | 1 | disputed | 1 |
| `Sheaf.Paper.ConstantCompletionCompletedFinitePull` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 8 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotients` | 8 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 8 | 1 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 8 | 8 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 9 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryFinitePull` | 9 | 1 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 10 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 10 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryPullComparison` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 11 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 11 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSecondCoordinateContraction` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTower` | 12 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 12 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelDerivedScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangle` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarTensorChainTower` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForward` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingReverse` | 14 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicActualNormalization` | 14 | 1 | proof | route |
| `Sheaf.Paper.FinitePerfectAdicConstantNormalization` | 15 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelReduction` | 17 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOrigin` | 17 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerEtaleDescent` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux` | 18 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjective` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatDetection` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberGeometry` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleRelativelyTrivialLineDescent` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleDiagonal` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjGluedSections` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedRelativeComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackLocalComparison` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | - | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryComparisonNormalization` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates` | - | 1 | proof | route |
| `Sheaf.CategoryTheory.TwistedActionUnderivedRestriction` | - | 1 | proof | route |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | - | 1 | proof | route |
| `Sheaf.Paper.AdicCompletedTensorRealizationDescent` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingCore` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingFunctoriality` | - | 1 | proof | route |
| `Sheaf.Paper.AdicReindexingTensor` | - | 1 | proof | route |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | - | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorCochains` | - | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | - | 1 | proof | route |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientInputLaws` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawInput` | - | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawOutputIdentity` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedOpenTensorContext` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedQuotientReductionPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.ConstructibleCompactSupportTargetIso` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceFiniteCartierChern` | - | 1 | proof | route |
| `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | - | 2 | proof | route |
| `Sheaf.Paper.ExceptionalIntegralSupportAdjoint` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalRingTransportFamily` | - | 1 | proof | route |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteDirectCounitFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteIntrinsicProjectionRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePartialTensorIdentityComposition` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteProperProjectionFixedRealization` | - | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorFixedCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteRingRefinementCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorRealizationCoefficientsEquality` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTotalTensorIsoComponentEquality` | - | 1 | proof | route |
| `Sheaf.Paper.IdentityFactorCoefficientComparison` | - | 1 | proof | route |
| `Sheaf.Paper.IdentityFactorFixedSupport` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | - | 15 | proof | route |
| `Sheaf.Paper.IntegralNormalizedRingRefinementLaws` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` | - | 1 | proof | route |
| `Sheaf.Paper.IntegralTensorPullbackAugmentation` | - | 1 | proof | route |
| `Sheaf.Paper.IntrinsicDirectCompositorCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.KummerStrictAdjunctCompatibility` | - | 1 | proof | route |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | - | 1 | proof | route |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedComplexes` | - | 1 | proof | route |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquare` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedScalarAssociatorLocalizationTransport` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityBaseChange` | - | 1 | proof | route |
| `Sheaf.Paper.OrdinaryPullbackCompositionEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.OrdinarySystemPullbackCompositorEvaluation` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization` | - | 1 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionComparisonExistence` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportCondition` | - | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalized` | - | 1 | proof | route |
| `Sheaf.Paper.RefinementOpenRestriction` | - | 1 | proof | route |
| `Sheaf.Paper.RingEndpointScalarRestrictions` | - | 1 | proof | route |
| `Sheaf.Paper.RingOpenMapInvertibility` | - | 1 | proof | route |
| `Sheaf.Paper.RingRefinementScalarWord` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 2 | proof | route |
| `Sheaf.Paper.SfDirectImageRestrictionPasting` | - | 1 | proof | route |
| `Sheaf.Paper.SystemFiniteRefinementMateCoordinates` | - | 1 | proof | route |
| `Sheaf.Paper.TensorReductionFiniteComponents` | - | 1 | proof | route |
| `Sheaf.Paper.TensorReductionStrictDerivedSquare` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralClassPullback` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralCoefficientPullbackExistence` | - | 1 | proof | route |
| `Sheaf.Paper.TowerOrdinaryScalarAssociation` | - | 1 | proof | route |
| `Sheaf.Paper.TowerReductionMateInvertible` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CanonicalReductionTensorPull` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison` | - | 1 | proof | route |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransport` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateResolving` | - | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility` | - | 1 | proof | route |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PublishedSystemTensorIdentification` | - | 1 | proof | route |
| `Sheaf.SixFunctors.PullQuotientOrdinaryProjection` | - | 1 | proof | route |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | - | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLift` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeDerivedExchangeComparison` | - | 1 | proof | route |
| `Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 11 | 2 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportQuotientComputationSquares` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | - | 2 | proof | 1 |
| `Sheaf.Paper.ExceptionalFiniteScalarMates` | - | 1 | proof | 1 |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | - | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 2 | proof | 1 |
| `Sheaf.Paper.ScalarExtensionQuotientAssociation` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | - | 1 | proof | 1 |
| `Sheaf.WeilSheaf.NativeOpenProperForgetting` | - | 4 | proof | 1 |
| `Sheaf.Algebra.Module.GradedLocalizationScalarExtension` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 4 | proof | 2 |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | - | 9 | proof | 2 |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | - | 3 | proof | 2 |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | - | 1 | proof | 3 |
| `Sheaf.Paper.SystemOperationExchangeRealization` | - | 7 | proof | 3 |

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
