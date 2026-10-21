# Work queue

78 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (12 clusters, 363 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `WeilConjectures.TraceFormula.WeilTrace` | 1 |  | error: WeilConjectures/TraceFormula/WeilTrace.lean: bad import 'WeilConjectures.TraceFormula.Main' |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 50, stage 3 1 items.

## Stage 1: nodes to split (7)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-norm-algcl-internal-hom-base-change` | 4012 | none |
| `lem-sfb-ramified-cartier-supported-purity` | 4013 | none |
| `lem-sfb-norm-completion-positive-cohomology-mono` | 4014 | none |
| `lem-sfb-supported-lattice-norm-projection` | 4014 | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (8)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-pur-affine-line-purity-comparison` | 1 | state | 14 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `det-prop-diagonal-tower-coefficients` | 1 | state | 2 |
| `lem-pe-internal-module-sectionwise-short-exact` | 1 | state | 0 |
| `lem-pur-affine-translation-trace` | 1 | state | 0 |
| `lem-pur-line-zero-class-etale-realization` | 1 | state | 0 |
| `lem-sfb-lattice-koszul-triangulated-cup-comparison` | 1 | state | 0 |
| `thm-pur-vector-bundle-thom` | 1 | state | 0 |

Not open yet: 372 nodes that below a finished node, not needed, 94 nodes that wait for a statement dependency (bottom-up), 6 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (45)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | repair | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | disputed | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 5 | 10 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 5 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | 5 | 5 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | 9 | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | 9 | 16 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | 10 | 1 | proof | 3 |
| `Sheaf.Paper.SbcCompletedOperations` | 10 | 15 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackReduction` | 7 | 4 | proof | 4 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 7 | 2 | proof | 4 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | 6 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | 11 | 1 | proof | 5 |
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
| `Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity` | - | 1 | proof | 16 |
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
