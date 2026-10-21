# Work queue

196 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (22 clusters, 954 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.SitePerfectComplex` | 1 |  | error: Sheaf/Paper/SitePerfectComplex.lean:122:10: failed to synthesize instance of type class |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.WeilTensorProduct` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.IntegralIndConstructibleHeartClosure` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.IntegralConstructibleCompactness` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FormalClosedSupport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ReductionOpenEtaleOrigin` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 87, stage 3 5 items.

## Stage 1: nodes to split (14)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-lisse-lattice-potential-kummer-tameness` | 4010 | none |
| `lem-sfb-tame-inertia-continuous-koszul` | 4010 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-root-tower-boundary-acyclicity` | 4011 | none |
| `lem-sfb-supported-finite-stage-topology-defect` | 4011 | none |
| `lem-sfb-cech-localization-unit-totalization` | 4012 | none |
| `lem-sfb-root-tower-inner-support` | 4012 | none |
| `lem-sfb-snc-tame-finite-fibre-classification` | 4012 | none |
| `lem-sfb-snc-universal-residual-charts` | 4012 | none |
| `lem-sfb-bicosimplicial-shuffle-totalization` | 4013 | none |
| `lem-sfb-snc-root-limit-normal-charts` | 4013 | none |
| `lem-pe-internal-module-sectionwise-short-exact` | - | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (26)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-tw-lisse-rational-realization` | 1 | state | 5 |
| `lem-sfb-integral-quotient-direct-image-comparison` | 1 | state | 2 |
| `lem-sfb-pointed-finite-etale-limit-cover` | 1 | state | 2 |
| `det-lem-stratified-lattice-scheme` | 1 | state | 0 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-fd-whole-tower-integral-pullback-comparison` | 1 | state | 0 |
| `lem-per-adic-normalized-fibre-comparisons` | 1 | state | 0 |
| `lem-pod-fixed-pair-truncation-cohomology` | 1 | state | 0 |
| `lem-pur-concentrated-support-etale-transfer` | 1 | state | 0 |
| `lem-sf-open-exchange-roos-restriction` | 1 | state | 0 |
| `lem-sfb-complete-group-torsor-monodromy` | 1 | state | 0 |
| `lem-sfb-condensed-derived-invariant-bar` | 1 | state | 0 |
| `lem-sfb-condensed-internal-bar-resolution` | 1 | state | 0 |
| `lem-sfb-condensed-product-bar-comparison` | 1 | state | 0 |
| `lem-sfb-derived-cech-image-totalization` | 1 | state | 0 |
| `lem-sfb-integral-ambient-tower-comparison` | 1 | state | 0 |
| `lem-sfb-integral-general-lfp-hom-finiteness` | 1 | state | 0 |
| `lem-sfb-internal-action-site-presentation` | 1 | state | 0 |
| `lem-sfb-partial-kummer-boundary-unit-model` | 1 | state | 0 |
| `lem-sfb-qlbar-internal-hom-coefficient-comparison` | 1 | state | 0 |
| `lem-sfb-root-tower-lisse-morphism-extension` | 1 | state | 0 |
| `lem-sfb-tame-root-tower-extension` | 1 | state | 0 |
| `lem-sfb-tame-stratum-kummer-descent` | 1 | state | 0 |
| `lem-sp-cofinal-finite-reduction-constructibility` | 1 | state | 0 |
| `lem-weil-point-derived-tensor-tower-coherence` | 1 | state | 0 |

Not open yet: 375 nodes that below a finished node, not needed, 107 nodes that wait for a statement dependency (bottom-up), 13 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (127)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | repair | route |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | repair | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | repair | route |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | 9 | 1 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
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
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 3 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | proof | 4 |
| `Sheaf.Paper.DerivedCompletedTensorBilinearity` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 4 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 4 |
| `Sheaf.Paper.PbcAutomorphismTransport` | - | 13 | proof | 4 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictQuotientExchangeUnitEquation` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 5 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.SliceTensorIntegerShiftCompatibility` | - | 3 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerExchange` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | - | 23 | proof | 5 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedScalarUnitAdjunction` | - | 1 | proof | 5 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | - | 21 | proof | 5 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.QuotientDiagramScalarProjection` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 1 | proof | 6 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 6 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest` | - | 4 | proof | 6 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 6 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 6 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 2 | proof | 6 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 6 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 6 |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | 4 | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 7 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedFiniteExchangeCoordinates` | - | 2 | proof | 7 |
| `Sheaf.Paper.CompletedKoszulReductionRoosTriangle` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 7 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 7 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 7 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 7 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 7 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 7 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 11 | 2 | proof | 8 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 8 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | - | 7 | proof | 8 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | proof | 8 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | proof | 8 |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | - | 1 | proof | 8 |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | - | 2 | proof | 8 |
| `Sheaf.Paper.WeilIndSheafCategory` | - | 8 | proof | 8 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` | - | 2 | proof | 9 |
| `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` | - | 1 | proof | 9 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 9 |
| `Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula` | - | 4 | proof | 9 |
| `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` | - | 1 | proof | 9 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | proof | 9 |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | - | 1 | proof | 9 |
| `Sheaf.Paper.IntegralAmbientOperationModels` | - | 4 | proof | 9 |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | proof | 9 |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | - | 1 | proof | 9 |
| `Sheaf.Paper.PointDerivedSectionsTensorDescent` | - | 1 | proof | 9 |
| `Sheaf.Paper.PointFiniteFreeSectionsTensor` | - | 1 | proof | 9 |
| `Sheaf.Paper.QuotientSystemMixedCoherence` | - | 3 | proof | 9 |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | - | 1 | proof | 9 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 9 |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | - | 1 | proof | 9 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 10 |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | - | 8 | proof | 10 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 10 |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | - | 1 | proof | 10 |
| `Sheaf.Paper.NormalizedOperationSystemModels` | - | 1 | proof | 10 |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | - | 1 | proof | 10 |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | - | 1 | proof | 10 |
| `Sheaf.Paper.ProEtaleScalarMateNormalization` | - | 3 | proof | 10 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 10 |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | - | 1 | proof | 10 |
| `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` | - | 1 | proof | 10 |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | - | 1 | proof | 10 |
| `Sheaf.CategoryTheory.TowerLimitTransposeNormalization` | - | 1 | proof | 11 |
| `Sheaf.Paper.CompletedTensorUnitInsertion` | - | 1 | proof | 11 |
| `Sheaf.Paper.PerfectQuotientExchangeNormalization` | - | 1 | proof | 11 |
| `Sheaf.Paper.QuotientDiagramProjectionEvaluation` | - | 1 | proof | 11 |
| `Sheaf.Paper.StrictQuotientDiagonalNormalization` | - | 1 | proof | 11 |
| `Sheaf.Paper.CompletionMateComparison` | - | 21 | proof | 12 |
| `Sheaf.Paper.SemilinearDerivedCalculus` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` | - | 5 | proof | 18 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 19 |

## Stage 3: waiting for statements of dependencies (2)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | `lem-weil-point-derived-tensor-tower-coherence` |

## Stage 3: held for an open upstream PR (5)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
