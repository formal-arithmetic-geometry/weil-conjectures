# Work queue

92 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (0 clusters, 3822 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.


Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 1, stage 3 58 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (2)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |

Not open yet: 1137 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (89)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 6 | 1 | disputed | 1 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 4 | 8 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 4 | 8 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 5 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 1 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 6 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionCompletedFinitePull` | 6 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionInverseImageExists` | 6 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorEvaluationCube` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 7 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionKoszulReflector` | 7 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare` | 7 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionFlatAndQuotients` | 8 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryFinitePull` | 8 | 1 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorKFlatNormalization` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarPullbackChainTower` | 8 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.ConstantCompletionOrdinaryPullComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarTensorChainTower` | 9 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionPullTransport` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSecondCoordinateContraction` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientScalarSectionComparisonExistence` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportCondition` | 10 | 1 | proof | route |
| `Sheaf.Paper.QuotientSectionTensorTransportNormalized` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux` | 11 | 1 | proof | route |
| `Sheaf.Paper.ConstantAdicQuotientModelReduction` | 11 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 11 | 1 | proof | route |
| `Sheaf.Paper.LisseFiniteQuotientEtaleOrigin` | 11 | 1 | proof | route |
| `Sheaf.Paper.LisseTowerEtaleDescent` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityBaseChange` | 12 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicSliceScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteModelDerivedScalarComparison` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangle` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientLayerLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteQuotientPreviousLocalComplexes` | 13 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForward` | 14 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingReverse` | 14 | 1 | proof | route |
| `Sheaf.Paper.KummerStrictAdjunctCompatibility` | 14 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 14 | 2 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientInputLaws` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawInput` | 15 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportQuotientRawOutputIdentity` | 15 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionQuotientAssociation` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatDetection` | 16 | 1 | proof | route |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | 16 | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | 16 | 21 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | 17 | 1 | proof | route |
| `Sheaf.Paper.TowerScalarFiniteBoundary` | 18 | 1 | proof | route |
| `Sheaf.TraceFormula.ScalarModelRoosZeroLift` | 18 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralClassPullback` | 19 | 1 | proof | route |
| `Sheaf.Paper.TowerReductionMateInvertible` | 20 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjective` | 21 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryComparisonNormalization` | 21 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation` | 21 | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralCoefficientPullbackExistence` | 21 | 1 | proof | route |
| `Sheaf.Paper.TowerOrdinaryScalarAssociation` | 21 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleRelativelyTrivialLineDescent` | 22 | 1 | proof | route |
| `Sheaf.Paper.CoefNativeOpenTensorCochains` | 22 | 1 | proof | route |
| `Sheaf.SixFunctors.OpenTensorProjectionMateResolving` | 23 | 1 | proof | route |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | 23 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberGeometry` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleDiagonal` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedRelativeComparison` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjSectionCompatibility` | 24 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjGluedSections` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine` | 25 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackLocalComparison` | 25 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionStrictDerivedSquare` | 27 | 1 | proof | route |
| `Sheaf.Paper.TensorReductionFiniteComponents` | 29 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedOpenTensorContext` | - | 1 | proof | route |
| `Sheaf.Paper.CompletedQuotientReductionPresentation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorRealizationCoefficientsEquality` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTotalTensorIsoComponentEquality` | - | 1 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 7 | 2 | proof | 1 |
| `Sheaf.Paper.CompactSupportQuotientComputationSquares` | 15 | 1 | proof | 1 |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | 17 | 2 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison` | - | 1 | proof | 1 |
| `Sheaf.Algebra.Module.GradedLocalizationScalarExtension` | - | 1 | proof | 2 |

## Stage 3: waiting for statements of dependencies (3)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | 12 | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
