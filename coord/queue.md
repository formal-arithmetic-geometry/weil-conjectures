# Work queue

132 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (14 clusters, 948 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.SitePerfectComplex` | 1 |  | error: Sheaf/Paper/SitePerfectComplex.lean:122:10: failed to synthesize instance of type class |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.IntegralConstructibleCompactness` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 90, stage 3 2 items.

## Stage 1: nodes to split (19)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-lisse-lattice-potential-kummer-tameness` | 4010 | none |
| `lem-sfb-discrete-lattice-koszul-resolution` | 4011 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-prime-to-ell-derived-invariants-reduction` | 4011 | none |
| `lem-sfb-condensed-derived-restriction-calculus` | 4012 | none |
| `lem-sfb-discrete-lattice-cup-exterior` | 4012 | none |
| `lem-sfb-integral-lisse-closed-base-change` | 4012 | none |
| `lem-sfb-norm-algcl-cohomology-topology-comparison` | 4012 | none |
| `lem-sfb-norm-algcl-internal-hom-base-change` | 4012 | none |
| `lem-sfb-profinite-constant-derived-functions` | 4012 | none |
| `lem-sfb-root-coordinate-supported-vanishing` | 4012 | none |
| `lem-sfb-trivial-ladic-derived-exterior` | 4012 | none |
| `lem-sfb-snc-tame-root-etale-extension` | 4013 | none |
| `lem-sfb-indfinite-contractible-base-wstrict` | 4014 | none |
| `lem-sfb-wstrict-lisse-component-cohomology` | 4014 | none |
| `sk-thm-pe-indetale-refinement` | - | none |
| `sk-thm-pe-wc-cover` | - | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (28)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-sfb-root-tower-boundary-acyclicity` | 1 | state | 1 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-fd-whole-tower-integral-pullback-comparison` | 1 | state | 0 |
| `lem-pe-internal-module-sectionwise-short-exact` | 1 | state | 0 |
| `lem-per-adic-normalized-fibre-comparisons` | 1 | state | 0 |
| `lem-sfb-cech-localization-unit-totalization` | 1 | state | 0 |
| `lem-sfb-condensed-derived-invariant-bar` | 1 | state | 0 |
| `lem-sfb-condensed-product-bar-comparison` | 1 | state | 0 |
| `lem-sfb-dense-lattice-derived-invariants-comparison` | 1 | state | 0 |
| `lem-sfb-faithfully-flat-normal-ring-descent` | 1 | state | 0 |
| `lem-sfb-finite-closed-cover-resolution` | 1 | state | 0 |
| `lem-sfb-integral-ambient-tower-comparison` | 1 | state | 0 |
| `lem-sfb-integral-general-lfp-hom-finiteness` | 1 | state | 0 |
| `lem-sfb-nonnegative-derived-totalization` | 1 | state | 0 |
| `lem-sfb-partial-kummer-boundary-unit-model` | 1 | state | 0 |
| `lem-sfb-qlbar-internal-hom-coefficient-comparison` | 1 | state | 0 |
| `lem-sfb-root-tower-coordinate-face` | 1 | state | 0 |
| `lem-sfb-root-tower-puncture-invariance` | 1 | state | 0 |
| `lem-sfb-simplex-lattice-shuffle-boundary` | 1 | state | 0 |
| `lem-sfb-snc-finite-root-regular-ring` | 1 | state | 0 |
| `lem-sfb-snc-tame-finite-fibre-classification` | 1 | state | 0 |
| `lem-sfb-snc-universal-residual-charts` | 1 | state | 0 |
| `lem-sfb-tame-root-tower-extension` | 1 | state | 0 |
| `lem-sfb-tame-stratum-kummer-descent` | 1 | state | 0 |
| `lem-zl-raw-heart-adic-lisse-stratification` | 1 | state | 0 |
| `lem-sfb-integral-quotient-projection-comparison` | 2 | state | 0 |
| `lem-sfb-tame-inertia-continuous-koszul` | 2 | state | 0 |

Not open yet: 374 nodes that below a finished node, not needed, 102 nodes that wait for a statement dependency (bottom-up), 18 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (63)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | repair | route |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | repair | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | repair | route |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | 9 | 1 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 3 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | - | 4 | proof | 3 |
| `Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | proof | 4 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 4 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 6 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 6 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 2 | proof | 6 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 6 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 7 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.FlatScalarTowerExchange` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedFiniteExchangeCoordinates` | - | 2 | proof | 7 |
| `Sheaf.Paper.CompletedScalarUnitAdjunction` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 7 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 7 |
| `Sheaf.Paper.QuotientDiagramScalarProjection` | - | 1 | proof | 7 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` | - | 5 | proof | 18 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 19 |

## Stage 3: waiting for statements of dependencies (1)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |

## Stage 3: held for an open upstream PR (2)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
