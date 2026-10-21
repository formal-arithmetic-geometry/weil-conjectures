# Work queue

127 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (12 clusters, 705 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ConstructibleCompactness` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ClosedSupportConstructible` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.RelativeSupportBottomDescent` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceModel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 63, stage 3 2 items.

## Stage 1: nodes to split (16)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-lisse-lattice-potential-kummer-tameness` | 4010 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-norm-algcl-internal-hom-base-change` | 4012 | none |
| `lem-sfb-normed-scalar-profinite-hom-acyclic` | 4013 | none |
| `lem-sfb-prime-to-ell-cochain-finite-quotient-descent` | 4013 | none |
| `lem-sfb-profinite-algcl-derived-invariants-comparison` | 4013 | none |
| `lem-sfb-ramified-cartier-supported-purity` | 4013 | none |
| `lem-sfb-torsion-acyclic-norm-coefficient-test` | 4013 | none |
| `lem-sfb-field-action-derived-section-transport` | 4014 | none |
| `lem-sfb-supported-lattice-norm-projection` | 4014 | none |
| `lem-sfb-ind-unipotent-procyclic-difference` | 4015 | none |
| `lem-sfb-internal-homogeneous-functions-injective` | 4015 | none |
| `lem-sfb-profinite-action-finite-quotients` | 4015 | none |
| `lem-sfb-qcqs-zero-dimensional-affine` | 4015 | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (29)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `sk-def-sf-orientation` | 2 | state | 17 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-pur-vector-integration-site-comparison` | 1 | state | 36 |
| `lem-sfb-condensed-derived-restriction-calculus` | 1 | state | 8 |
| `det-prop-diagonal-tower-coefficients` | 1 | state | 2 |
| `lem-sf-open-external-tensor-normalization` | 1 | state | 2 |
| `lem-sfb-condensed-galois-global-descent` | 1 | state | 2 |
| `lem-sfb-root-tower-boundary-acyclicity` | 1 | state | 1 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-coef-compact-support-normalized-realization` | 1 | state | 0 |
| `lem-fix-compactification-completed-realization` | 1 | state | 0 |
| `lem-pe-internal-module-sectionwise-short-exact` | 1 | state | 0 |
| `lem-per-adic-normalized-fibre-comparisons` | 1 | state | 0 |
| `lem-pur-dualizing-unit-composite` | 1 | state | 0 |
| `lem-sf-open-projection-roos-completion` | 1 | state | 0 |
| `lem-sfb-action-topos-geometric-restriction` | 1 | state | 0 |
| `lem-sfb-acyclic-hypercover-pullback-normalization` | 1 | state | 0 |
| `lem-sfb-closed-test-derived-exchange-model` | 1 | state | 0 |
| `lem-sfb-derived-invariants-normal-subgroup-comparison` | 1 | state | 0 |
| `lem-sfb-field-profinite-galois-site` | 1 | state | 0 |
| `lem-sfb-integral-cubical-chain-diagonal` | 1 | state | 0 |
| `lem-sfb-polynomial-derived-bar-comparison` | 1 | state | 0 |
| `lem-sfb-poset-augmented-chain-prism` | 1 | state | 0 |
| `lem-sfb-prime-to-ell-derived-invariants-reduction` | 1 | state | 0 |
| `lem-sfb-product-chain-proper-interval-homology` | 1 | state | 0 |
| `lem-sfb-snc-tame-finite-fibre-classification` | 1 | state | 0 |
| `lem-sfb-tame-stratum-kummer-descent` | 1 | state | 0 |
| `lem-zl-constant-geometric-stalk-unit` | 1 | state | 0 |
| `lem-sfb-profinite-constant-derived-functions` | 2 | state | 0 |

Not open yet: 373 nodes that below a finished node, not needed, 110 nodes that wait for a statement dependency (bottom-up), 15 nodes that wait for stage 1 (statement downstream not grounded).

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
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
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
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 6 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 6 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 1 | proof | 6 |
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
| `Sheaf.Paper.NormalizedFiniteComparisonExistence` | - | 1 | proof | 7 |
| `Sheaf.Paper.QuotientDiagramScalarProjection` | - | 1 | proof | 7 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` | - | 5 | proof | 18 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 19 |

## Stage 3: held for an open upstream PR (2)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
