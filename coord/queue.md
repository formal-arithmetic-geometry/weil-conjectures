# Work queue

40 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (1 clusters, 4051 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralProperReductionBound` | 1 |  | error: Sheaf/Paper/IntegralProperReductionBound.lean:114:9: failed to synthesize | ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topo |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 0, stage 3 1 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (2)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-pur-general-legacy-hom-coordinates` | 1 | state | 2 |
| `lem-zl-finite-separable-tensor-primitive-presentation` | 1 | state | 0 |

Not open yet: 1138 nodes that below a finished node, not needed, 2 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (36)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | - | 1 | disputed | route |
| `Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives` | 10 | 1 | disputed | 1 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | 8 | 10 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 8 | 8 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 9 | 2 | proof | route |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 10 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | 10 | 3 | proof | route |
| `Sheaf.Paper.FinitePullbackTensorQuotientRepresentatives` | 10 | 1 | proof | route |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | 10 | 1 | proof | route |
| `Sheaf.Paper.AmbientPullbackTensorCoherence` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTowerCore` | 11 | 2 | proof | route |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | 11 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports` | 12 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackStrictFiniteComponent` | 12 | 1 | proof | route |
| `Sheaf.Paper.PrimitiveQuotientScalarModelExistence` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperShriekCompSupports` | 14 | 1 | proof | route |
| `Sheaf.Paper.RamifiedCoefficientModuleBaseChange` | 17 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux` | 18 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus` | - | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryComparisonNormalization` | - | 1 | proof | route |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | - | 1 | proof | route |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | - | 26 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation` | - | 1 | proof | route |
| `Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedChernFiniteBoundary` | - | 1 | proof | route |
| `Sheaf.Paper.NormalizedVectorPurityBaseChange` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | - | 21 | proof | route |
| `Sheaf.Paper.QcqsCompactSupportNativeTowerComparison` | - | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 3 | proof | route |
| `Sheaf.Paper.TowerChernReductionPullback` | - | 1 | proof | route |
| `Sheaf.Paper.TowerClassLinePullbackHorizontal` | - | 1 | proof | route |
| `Sheaf.Paper.TowerIntegralClassPullback` | - | 1 | proof | route |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | - | 2 | proof | 1 |
| `Sheaf.Paper.PodReindexingHomResolutionModel` | - | 1 | proof | 1 |

## Stage 3: waiting for statements of dependencies (3)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` | 3 | 1 | `lem-per-adic-closed-constructible` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 10 | 5 | `lem-pur-general-legacy-hom-coordinates` |
| `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` | - | 1 | `lem-zl-finite-separable-tensor-primitive-presentation` |
