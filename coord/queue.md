# Work queue

384 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (13 clusters, 2095 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 1 |  | error: failed in the global build (no message located) |
| `Sheaf.Paper.AdicStratifiedPerfect` | 1 |  | error: Sheaf/Paper/AdicStratifiedPerfect.lean:209:8: Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexQcqsHomologyMono.lean:59:15: Unknown identifier `SingleComplexBaseChange.StalkCondition` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.CategoryTheory.MappedSmartTruncationTower` | 1 |  | error: Sheaf/CategoryTheory/MappedSmartTruncationTower.lean:5:0: error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed, environment already con |
| `Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 187, stage 3 186 items.

## Stage 1: nodes to split (11)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-constructible-closed-base-change` | 2005 | none |
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-continuous-algcl-open-scalar-comparison` | 4008 | none |
| `lem-sfb-normal-continuous-algcl-monodromy` | 4009 | none |
| `lem-sfb-cohomology-tor-interval` | - | none |
| `lem-zl-constant-sheaf-weight-zero` | - | none |
| `lem-pod-stratified-dualizable-bounded` | - | none |
| `lem-pod-stratified-dualizable-hom-continuity` | - | none |
| `def-per-support-condition` | - | none |
| `lem-dl-a1-galois-prime-residue-lifting` | - | none |
| `lem-dl-a1-integral-normal-residue-etale-splitting` | - | none |

## Stage 2: nodes to state (29)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-weil-point-finite-free-sections-tensor` | 1 | state | 2 |
| `sk-thm-picard-duality` | 1 | state | 2 |
| `lem-sp-ell-coefficient-fiber` | 1 | state | 1 |
| `lem-dl-a1-finite-group-inertia-invariants-etale` | 1 | state | 0 |
| `lem-pc-curve-local-scalar-principal-parts` | 1 | state | 0 |
| `lem-pc-finite-dimensional-trace-exact` | 1 | state | 0 |
| `lem-pur-exact-pullback-signed-comparison` | 1 | state | 0 |
| `lem-pur-finite-product-derived-tensor-calculus` | 1 | state | 0 |
| `lem-pur-quotient-expression-kflat-normalization` | 1 | state | 0 |
| `lem-pur-sequence-adjoint-resolution-shifts` | 1 | state | 0 |
| `lem-pur-strict-coefficient-comparison-calculus` | 1 | state | 0 |
| `lem-sf-boundary-bounded-tensor-comparison` | 1 | state | 0 |
| `lem-sf-clopen-lisse-complete-localization` | 1 | state | 0 |
| `lem-sf-perfect-tensor-roos-completion` | 1 | state | 0 |
| `lem-sf-point-ringed-evaluation-model` | 1 | state | 0 |
| `lem-sf-strict-dvr-reduction-triangles` | 1 | state | 0 |
| `lem-sfb-continuous-frame-sheaf-comparison` | 1 | state | 0 |
| `lem-sfb-ordinary-proetale-direct-image-plus-comparison` | 1 | state | 0 |
| `lem-sfb-reduction-single-cohomology-normalization` | 1 | state | 0 |
| `lem-sfb-scalar-hom-chain-coefficient-coherence` | 1 | state | 0 |
| `lem-sp-power-torsion-sheaf-limit-complete` | 1 | state | 0 |
| `lem-sp-semilinear-kflat-tower-model` | 1 | state | 0 |
| `lem-trf-section-coordinate-counit-normalization` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-strict-tower-transport` | 1 | state | 0 |
| `lem-weil-pbc-flat-scalar-tower-exchange` | 1 | state | 0 |
| `lem-weil-pbc-raw-restricted-class-normalization` | 1 | state | 0 |
| `lem-zl-dualizable-categorical-trace-conjugacy` | 1 | state | 0 |
| `sk-thm-picard-rr` | 1 | state | 0 |

Not open yet: 355 nodes that below a finished node, not needed, 8 nodes that wait for stage 1 (statement downstream not grounded), 124 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (322)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | - | 1 | repair | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice` | - | 1 | proof | 1 |
| `Sheaf.Paper.InternalScalarTensorComparison` | - | 2 | proof | 1 |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | - | 2 | proof | 1 |
| `Sheaf.Paper.SquareZeroPeriodicTensor` | - | 2 | proof | 1 |
| `Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor` | - | 4 | proof | 2 |
| `Sheaf.Algebra.Homology.InternalHomLocalizationComparison` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.RHomContinuityTriangleClosure` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.CompactificationMiddleOverBase` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ConstantFieldTorBounds` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.LocalFinitePresentationInverseImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SfEtaleOriginPushforwardAmplitude` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.CommonStageKaroubiInverse` | - | 9 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedBelowHomTest` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantPeriodicResolutionNonzero` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | - | 2 | proof | 2 |
| `Sheaf.Paper.EtaleDerivedDirectImageCoherence` | - | 1 | proof | 2 |
| `Sheaf.Paper.ExactScalarPeriodicResolution` | - | 6 | proof | 2 |
| `Sheaf.Paper.FiniteProEtalePushforwardConstructible` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.PeriodicTensorNormalForm` | - | 1 | proof | 2 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 2 |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FieldComplexCohomologySplitting` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.FixedTensorLocalizationComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatDvrScalarTensor` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.IndFiniteFreeScalarModel` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatScalarTowerRealization` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.OneKFlatChainTranspose` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RHomColimitSourceTransport` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.DirectImageScalarRestrictionCocycle` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleChartLeftCompositor` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` | - | 7 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SectionReesNoetherianGeometry` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.AdicBasisLimit` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.ClosedEvaluationDualCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoherentCoconeNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ScalarPerfectCohomologyAndPidModels` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.EquivalenceAdjunctionComparison` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.EquivariantCoequalizerComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactLinearKoszulFibre` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FullyFaithfulExceptionalHomTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.InternalAbelianFiniteLimitCreation` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.LocalizedBasisCoefficients` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Monoidal.AdjunctionEquivalenceTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.MonoidalBalancingDiagrams` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.NormalizedRoosShiftComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares` | - | 18 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedCompositorUnitNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorSquareMateFactorization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedPullbackLinear` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarCoordinateLimitCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SectionRingLaxPushforwardCoherence` | - | 11 | proof | 3 |
| `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.WeakSerreBoundedThick` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.WordReconstructionCoherence` | - | 1 | proof | 3 |
| `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages` | - | 1 | proof | 3 |
| `Sheaf.Paper.BoundaryEtaleAdjunctionRestriction` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientComplexRationalization` | - | 6 | proof | 3 |
| `Sheaf.Paper.ContinuousCoefficientSliceNormalization` | - | 2 | proof | 3 |
| `Sheaf.Paper.FiniteCompactSupportUniformTor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldStratifiedGeneration` | - | 1 | proof | 3 |
| `Sheaf.Paper.FlatCommonQuotientReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralAmbientOperationModels` | - | 10 | proof | 3 |
| `Sheaf.Paper.IntegralCoefficientPresentationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelOpenClosedPieces` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | - | 2 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 4 | proof | 3 |
| `Sheaf.Paper.OpenFiniteConstructibilityInterval` | - | 1 | proof | 3 |
| `Sheaf.Paper.PrincipalKoszulStrictReplacement` | - | 6 | proof | 3 |
| `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible` | - | 3 | proof | 3 |
| `Sheaf.Paper.QuotientScalarComparisonDescent` | - | 2 | proof | 3 |
| `Sheaf.Paper.RHomColimitCohomologyLadder` | - | 4 | proof | 3 |
| `Sheaf.Paper.RingedTensorAdjunctionMate` | - | 1 | proof | 3 |
| `Sheaf.Paper.SectionExceptionalFibreCoherence` | - | 5 | proof | 3 |
| `Sheaf.Paper.SectionLocalDualizingComparisons` | - | 1 | proof | 3 |
| `Sheaf.Paper.SectionReesBaseChangeEtale` | - | 6 | proof | 3 |
| `Sheaf.Paper.SequenceSiteCompletionProjection` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictPerfectRingedPullbackModel` | - | 3 | proof | 3 |
| `Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | proof | 3 |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatConstantScalarMono` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.BoundedProjectiveComplexDualPairing` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` | - | 6 | proof | 4 |
| `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedTensorComplexConstraints` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.ScalarHomChainEvaluation` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SubcategoryLeftResolution` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientFlatComplexSequence` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorSignedCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteConstantMapNaturality` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.OpenSourceComposition` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | - | 9 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalizedRingMateGraphEvaluation` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | - | 6 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange` | - | 7 | proof | 4 |
| `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AdditiveLocalizationDescent` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.AdjointEquivalenceConjugation` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.CofinalRoosRestriction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedTowerCounitProjections` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactSquareDerivedCounit` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.InjectiveTowerRoosShifts` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveExactSquareComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjectCokernelAction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjects.KernelStructure` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RegularScalarExtensionMultiplication` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingLocalizationSheafification` | - | 5 | proof | 4 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedTripleResolutionFormulas` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompatibleCoefficientTower` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletionUnitStrictQuotientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedTowerEvaluationNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExactSectionsReductionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.FlatScalarDirectImageLimitCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.FlatSingleScalarConventions` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntrinsicFiniteDerivedPullback` | - | 5 | proof | 4 |
| `Sheaf.Paper.ProjectiveCohomologySplitModel` | - | 3 | proof | 4 |
| `Sheaf.Paper.ProjectiveTopCellAttachment` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurAdicLineSystemBaseChange` | - | 1 | proof | 4 |
| `Sheaf.Paper.SectionLocalComparisonData` | - | 2 | proof | 4 |
| `Sheaf.Paper.SheafTensorIdealQuotient` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictHomNumeratorTranspose` | - | 1 | proof | 4 |
| `Sheaf.ProperBaseChange.SingletonSiteModuleComparison` | - | 1 | proof | 4 |
| `Sheaf.RingTheory.ProEtale.HenselianClosedLift` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.CompletedCoefficientFreeResolution` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalAmplitude` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalBoundedSums` | - | 6 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalNeighborhoodVanishing` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.BalancedTensorChain` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.DVRProjectiveComplexMatrixModel` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus` | - | 11 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.SliceTensorIntegerShiftCompatibility` | - | 3 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CoordinateChartFiniteDimensionWitness` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleStalkTotalTensorComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GenericComponentSiteComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing` | - | 3 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization` | - | 3 | proof | 5 |
| `Sheaf.CategoryTheory.Adjunction.LeftCoefficientProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.AdjunctionSquareShiftMate` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.CompositeLeftProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.CompositeRelativeTensorAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.DerivedSquareShiftOnKInjectives` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization` | - | 7 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor` | - | 5 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.ExactDerivedTransformationPasting` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FiniteRingActionLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.NormalizedAdjunctionSquareTranspose` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.OpenLeftProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RoosTransitionHomotopy` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SheafTensorUnitComparison` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.TensorActionTraceContraction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.UnitAdjunctTensorAction` | - | 1 | proof | 5 |
| `Sheaf.NumberTheory.Padics.FiniteSumLattice` | - | 1 | proof | 5 |
| `Sheaf.Paper.ComponentRelativeProfiniteSite` | - | 1 | proof | 5 |
| `Sheaf.Paper.ConstructibleLocalizingDetermination` | - | 1 | proof | 5 |
| `Sheaf.Paper.ContinuousLatticeSum` | - | 1 | proof | 5 |
| `Sheaf.Paper.PuritySupportCommonInjectives` | - | 1 | proof | 5 |
| `Sheaf.Paper.StrictQuotientScalarBalancing` | - | 1 | proof | 5 |
| `Sheaf.RingTheory.HenselianWStrictLocalInvariance` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness` | - | 6 | proof | 5 |
| `Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.KFlatShortExactQuotient` | - | 1 | proof | 6 |
| `Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EffectiveCartierAffineDimensionDrop` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.SplitFibreProjections` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.UnboundedKFlatResolution` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.ExactAdjointTowerModels` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.PartitionRefinementSheafification` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation` | - | 1 | proof | 6 |
| `Sheaf.FieldTheory.SepClosedAlgebrasTensorIrreducible` | - | 1 | proof | 6 |
| `Sheaf.Paper.ClassicalLocalizationTriangleTransport` | - | 1 | proof | 6 |
| `Sheaf.Paper.CommonLinePositiveScalarPowers` | - | 2 | proof | 6 |
| `Sheaf.Paper.ComparisonGlobalResolutionModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.DerivedLocalClassEdgeComparison` | - | 1 | proof | 6 |
| `Sheaf.Paper.EtaleLowerTruncationFlatModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarTensorTower` | - | 7 | proof | 6 |
| `Sheaf.RingTheory.HenselianSmoothAlgebraLifting` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.GeometricTwoIsoScalarPairing` | - | 1 | proof | 6 |
| `Sheaf.Topology.FiniteQuotientFiberProduct` | - | 1 | proof | 6 |
| `Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleQuotientTensorStalkCriterion` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.SupportQuotientPairPullback` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.SemilinearTensorPresentationTransport` | - | 1 | proof | 7 |
| `Sheaf.Compactification.NagataDensityNormalizationSetup` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedCoefficientTensorNormalization` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SplitPerfectDualTorWindow` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined` | - | 1 | proof | 8 |
| `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact` | - | 1 | proof | 8 |
| `Sheaf.Paper.ScalarPerfectDualRealization` | - | 10 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.CoherentHigherImageClasses` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation` | - | 2 | proof | 18 |
| `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf` | - | 1 | proof | 18 |

## Stage 3: waiting for statements of dependencies (23)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | `lem-zl-constant-geometric-stalk-unit` |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | - | 1 | `lem-sfb-scalar-hom-chain-coefficient-coherence` |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | `lem-weil-pbc-raw-restricted-class-normalization` |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | - | 2 | `lem-sf-locally-closed-relative-transpose-normalization` |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | `lem-pur-support-comparison-section-model` |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | - | 4 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | `lem-coef-enriched-sequence-projection-formula` |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 7 | `lem-cbc-completed-open-strict-mate-identification` |
| `Sheaf.Paper.CompletedDirectImageLimits` | - | 2 | `lem-weil-pbc-augmented-diagram-projection-mate` |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | `lem-pur-strict-quotient-diagonal-normalization` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-pulled-reduction-normalization-comparison` |
| `Sheaf.Paper.ExternalEvaluationTransposeNatural` | - | 1 | `lem-pur-exact-pullback-signed-comparison` |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | `lem-a1-roos-intrinsic-unit-comparison` |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | `lem-sf-point-ringed-evaluation-model` |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | `lem-weil-point-finite-free-sections-tensor` |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | `lem-pur-sequence-adjoint-resolution-shifts` |
| `Sheaf.Paper.QcqsProperHullTailBound` | - | 1 | `lem-sfb-qcqs-proper-serre-heart-bound` |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | - | 1 | `lem-weil-pbc-augmented-diagram-projection-mate` |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | `lem-sf-cbc-localized-strict-tensor-descent` |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | `lem-sf-completed-pullback-mate-factorization` |
| `Sheaf.SixFunctors.AdmissibleTensorConstructibility` | - | 1 | `lem-sfb-continuous-qbar-constructible-generators` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | - | 2 | `lem-sfb-integral-localization-hom-colimit` |

## Stage 3: held for an open upstream PR (17)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
