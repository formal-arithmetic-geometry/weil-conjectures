# Work queue

63 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (9 clusters, 360 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.TensorCoordinateIdentifications` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 53, stage 3 1 items.

## Stage 1: nodes to split (5)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-ramified-cartier-supported-purity` | 4013 | none |
| `lem-sfb-norm-completion-positive-cohomology-mono` | 4014 | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (4)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-pur-affine-space-comparison` | 1 | state | 10 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-pe-internal-module-sectionwise-short-exact` | 1 | state | 0 |
| `thm-pur-vector-bundle-thom` | 1 | state | 0 |

Not open yet: 371 nodes that below a finished node, not needed, 92 nodes that wait for a statement dependency (bottom-up), 4 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (40)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | disputed | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 5 | 10 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 5 | proof | route |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 4 | proof | 4 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 1 | proof | 6 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 7 | proof | 6 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 6 |
| `Sheaf.CategoryTheory.FlatScalarTowerExchange` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 7 |
| `Sheaf.Paper.NormalizedFiniteComparisonExistence` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 19 |

## Stage 3: held for an open upstream PR (2)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
