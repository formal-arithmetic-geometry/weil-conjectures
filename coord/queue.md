# Work queue

768 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (21 clusters, 1072 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | 1 |  | error: Sheaf/Paper/IntegralConstructibleSequentialHom.lean:114:16: Unknown identifier `constructible_of_iso` |
| `Sheaf.Paper.FdCoefficientComparison` | 1 |  | error: Sheaf/Paper/FdCoefficientComparison.lean:195:2: failed to synthesize instance of type class |
| `Sheaf.Paper.SitePerfectComplex` | 1 |  | error: Sheaf/Paper/SitePerfectComplex.lean:122:10: failed to synthesize instance of type class |
| `Sheaf.Paper.AdicStratifiedPerfect` | 1 |  | error: Sheaf/Paper/AdicStratifiedPerfect.lean:209:8: Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:134:10: Unknown identifier `factors` |
| `Sheaf.SixFunctors.ClosedImmersionTensorProjection` | 1 |  | error: Sheaf/SixFunctors/ClosedImmersionTensorProjection.lean:47:4: Type mismatch: After simplification, term |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexQcqsHomologyMono.lean:59:15: Unknown identifier `SingleComplexBaseChange.StalkCondition` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.CategoryTheory.MappedSmartTruncationTower` | 1 |  | error: Sheaf/CategoryTheory/MappedSmartTruncationTower.lean:5:0: error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed, environment already con |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | 1 |  | error: Sheaf/Paper/ExtensionZeroStratifiedPerfect.lean:87:9: Unknown identifier `LocallyClosedStratification` |
| `Sheaf.Algebra.Homology.IntegralBoundedKunnethExact` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | 1 |  | error: Sheaf/Paper/FiniteDiscreteCoefficientSquareCoherence.lean:254:6: Unknown constant `AlgebraicGeometry.Etale.pullbackSquareComparison_def` |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: Sheaf/Paper/CondensedQbarPullbackCube.lean:121:40: Unknown identifier `finiteCoefficientDerivedToAlgCl` |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 138, stage 3 15 items.

## Stage 1: nodes to split (17)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-proper-constructible-closed-base-change` | 2005 | none |
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-zl-dualizable-categorical-trace-conjugacy` | 2008 | none |
| `lem-pc-curve-local-scalar-principal-parts` | 3017 | none |
| `lem-pc-tate-residue-exact-sequence` | 3017 | none |
| `lem-pc-finite-dimensional-trace-exact` | 3018 | none |
| `lem-sfb-continuous-algcl-open-scalar-comparison` | 4008 | none |
| `lem-sfb-normal-continuous-algcl-monodromy` | 4009 | none |
| `lem-sfb-cohomology-tor-interval` | - | none |
| `lem-zl-constant-sheaf-weight-zero` | - | none |
| `det-sp-composition-factors` | - | none |
| `lem-pod-condensed-localization-hom` | - | none |
| `def-sfb-tensor-symmetry-pure-equation` | - | none |
| `lem-pod-isomorphism-scalar-comparison-agreement` | - | none |
| `def-per-support-condition` | - | none |
| `lem-dl-a1-finite-group-inertia-invariants-etale` | - | none |
| `lem-dl-a1-galois-prime-residue-lifting` | - | none |

## Stage 2: nodes to state (115)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-pur-completed-primitive-counit-comparison` | 2 | state | 4 |
| `lem-pc-tate-abstract-residue-calculus` | 1 | state | 2 |
| `lem-per-adic-common-stage-truncations` | 1 | state | 2 |
| `lem-per-rational-realization-pullback-comparison` | 1 | state | 2 |
| `lem-weil-pbc-strict-quotient-scalar-balancing` | 1 | state | 2 |
| `lem-weil-point-finite-free-sections-tensor` | 1 | state | 2 |
| `sk-thm-picard-duality` | 1 | state | 2 |
| `lem-pc-finite-potent-trace-calculus` | 1 | state | 1 |
| `lem-pur-strict-quotient-diagonal-normalization` | 1 | state | 1 |
| `lem-sf-exact-pullback-counit-normalization` | 1 | state | 1 |
| `lem-sfb-scalar-reduction-unit-triangle` | 1 | state | 1 |
| `lem-sp-ell-coefficient-fiber` | 1 | state | 1 |
| `lem-weil-isomorphism-scalar-tensor-kflat-model` | 1 | state | 1 |
| `lem-weil-pbc-augmented-diagram-projection-mate` | 1 | state | 1 |
| `lem-weil-pbc-flat-scalar-tower-limit-square` | 1 | state | 1 |
| `det-nagata-density-normalization-pushforward` | 1 | state | 0 |
| `lem-a1-completed-perfect-scalar-pullback` | 1 | state | 0 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-a1-integral-stratum-chart-restrictions` | 1 | state | 0 |
| `lem-a1-point-realization-standard-cohomology` | 1 | state | 0 |
| `lem-a1-roos-intrinsic-unit-comparison` | 1 | state | 0 |
| `lem-a1-texact-coefficient-stage-descent` | 1 | state | 0 |
| `lem-cbc-completed-open-strict-mate-identification` | 1 | state | 0 |
| `lem-cbc-ringed-open-scalar-limit-coherence` | 1 | state | 0 |
| `lem-coef-enriched-sequence-projection-formula` | 1 | state | 0 |
| `lem-dl-a1-henselian-global-inertia-comparison` | 1 | state | 0 |
| `lem-dl-a1-inertia-restriction-surjective` | 1 | state | 0 |
| `lem-fix-proper-etale-origin-scalar-isomorphism` | 1 | state | 0 |
| `lem-pc-tate-adelic-reciprocity` | 1 | state | 0 |
| `lem-pd-section-derived-open-adjunction-normalization` | 1 | state | 0 |
| `lem-pd-section-derived-tensor-normalization` | 1 | state | 0 |
| `lem-per-constructible-rational-hom-comparison` | 1 | state | 0 |
| `lem-per-continuous-coefficient-slice-normalization` | 1 | state | 0 |
| `lem-per-rational-realization-degree-reflection` | 1 | state | 0 |
| `lem-pod-fixed-pair-truncation-cohomology` | 1 | state | 0 |
| `lem-pur-affine-coordinate-support-stalk-continuity` | 1 | state | 0 |
| `lem-pur-concentrated-support-etale-transfer` | 1 | state | 0 |
| `lem-pur-coordinate-chart-finite-dimension-witness` | 1 | state | 0 |
| `lem-pur-etale-kflat-support-comparison` | 1 | state | 0 |
| `lem-pur-etale-sum-right-adjoint-tensor` | 1 | state | 0 |
| `lem-pur-exact-pullback-signed-comparison` | 1 | state | 0 |
| `lem-pur-finite-open-product-swap` | 1 | state | 0 |
| `lem-pur-finite-product-derived-tensor-calculus` | 1 | state | 0 |
| `lem-pur-finite-product-field-coefficient-descent` | 1 | state | 0 |
| `lem-pur-finite-type-coordinate-support-orientation` | 1 | state | 0 |
| `lem-pur-injective-tower-roos-shifts` | 1 | state | 0 |
| `lem-pur-inverse-image-scalar-unit-normalization` | 1 | state | 0 |
| `lem-pur-normalized-operation-system-models` | 1 | state | 0 |
| `lem-pur-normalized-scalar-comparison-realization` | 1 | state | 0 |
| `lem-pur-origin-class-projective-comparison` | 1 | state | 0 |
| `lem-pur-proetale-direct-image-global-evaluation` | 1 | state | 0 |
| `lem-pur-quotient-diagram-projection-evaluation` | 1 | state | 0 |
| `lem-pur-quotient-expression-kflat-normalization` | 1 | state | 0 |
| `lem-pur-sequence-adjoint-resolution-shifts` | 1 | state | 0 |
| `lem-pur-sequence-site-open-extension` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-pur-signed-line-scalar-pullback-square` | 1 | state | 0 |
| `lem-pur-strict-coefficient-comparison-calculus` | 1 | state | 0 |
| `lem-pur-support-comparison-section-model` | 1 | state | 0 |
| `lem-pur-total-tensor-signed-coherence` | 1 | state | 0 |
| `lem-pur-tower-limit-transpose-normalization` | 1 | state | 0 |
| `lem-sf-boundary-bounded-tensor-comparison` | 1 | state | 0 |
| `lem-sf-cbc-localized-strict-tensor-descent` | 1 | state | 0 |
| `lem-sf-clopen-lisse-complete-localization` | 1 | state | 0 |
| `lem-sf-complete-top-residue-cell-cone` | 1 | state | 0 |
| `lem-sf-completed-coefficient-free-resolution` | 1 | state | 0 |
| `lem-sf-derived-completed-tensor-bilinearity` | 1 | state | 0 |
| `lem-sf-locally-closed-closure-adjoint-realization` | 1 | state | 0 |
| `lem-sf-locally-closed-closure-comparison-square` | 1 | state | 0 |
| `lem-sf-open-quotient-koszul-completeness` | 1 | state | 0 |
| `lem-sf-open-roos-unit-adjunction` | 1 | state | 0 |
| `lem-sf-perfect-scalar-tensor-coherence` | 1 | state | 0 |
| `lem-sf-perfect-tensor-roos-completion` | 1 | state | 0 |
| `lem-sf-point-ringed-evaluation-model` | 1 | state | 0 |
| `lem-sf-projective-cohomology-split-model` | 1 | state | 0 |
| `lem-sf-strict-dvr-reduction-triangles` | 1 | state | 0 |
| `lem-sf-tensor-comparison-localization-descent` | 1 | state | 0 |
| `lem-sfb-continuous-algcl-stratified-finite-models` | 1 | state | 0 |
| `lem-sfb-continuous-frame-sheaf-comparison` | 1 | state | 0 |
| `lem-sfb-finite-flat-constructible-total-tensor` | 1 | state | 0 |
| `lem-sfb-intrinsic-finite-derived-pullback` | 1 | state | 0 |
| `lem-sfb-ordinary-proetale-direct-image-plus-comparison` | 1 | state | 0 |
| `lem-sfb-periodic-tensor-normal-form` | 1 | state | 0 |
| `lem-sfb-scalar-hom-chain-coefficient-coherence` | 1 | state | 0 |
| `lem-sp-koszul-roos-projection-comparison` | 1 | state | 0 |
| `lem-sp-power-torsion-sheaf-limit-complete` | 1 | state | 0 |
| `lem-sp-semilinear-kflat-tower-model` | 1 | state | 0 |
| `lem-sp-subterminal-derived-image-calculus` | 1 | state | 0 |
| `lem-sp-subterminal-module-local-calculus` | 1 | state | 0 |
| `lem-trf-completion-unit-strict-quotient-model` | 1 | state | 0 |
| `lem-trf-isomorphism-multiplication-cone-descent` | 1 | state | 0 |
| `lem-trf-section-coordinate-counit-normalization` | 1 | state | 0 |
| `lem-trf-section-local-dualizing-comparisons` | 1 | state | 0 |
| `lem-trf-section-rees-noetherian-geometry` | 1 | state | 0 |
| `lem-weil-coefficient-complex-rationalization` | 1 | state | 0 |
| `lem-weil-constant-scalar-unit-quasi-isomorphism` | 1 | state | 0 |
| `lem-weil-pbc-affine-cohomology-etale-module-realization` | 1 | state | 0 |
| `lem-weil-pbc-derived-tensor-shift-descent` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-strict-tower-transport` | 1 | state | 0 |
| `lem-weil-pbc-flat-scalar-tower-exchange` | 1 | state | 0 |
| `lem-weil-pbc-proetale-closed-underived-projection` | 1 | state | 0 |
| `lem-weil-pbc-pulled-reduction-normalization-comparison` | 1 | state | 0 |
| `lem-weil-pbc-raw-restricted-class-normalization` | 1 | state | 0 |
| `lem-weil-pbc-slice-tensor-integer-shift-compatibility` | 1 | state | 0 |
| `lem-weil-ramified-pullback-tower-identification` | 1 | state | 0 |
| `lem-weil-scalar-pullback-strict-cone-naturality` | 1 | state | 0 |
| `lem-zl-bertini-finite-cover-irreducible-system` | 1 | state | 0 |
| `lem-zl-bertini-prescribed-point-smooth-system` | 1 | state | 0 |
| `lem-zl-condensed-stalk-frobenius-orbit-trace` | 1 | state | 0 |
| `sk-lem-as-properties` | 1 | state | 0 |
| `sk-thm-picard-rr` | 1 | state | 0 |
| `lem-pod-pullback-identities-scalar-extension` | 2 | state | 0 |
| `lem-trf-counit-realization-substitution` | 2 | state | 0 |
| `lem-weil-point-automorphism-transport-scalar-extension` | 2 | state | 0 |

Not open yet: 355 nodes that below a finished node, not needed, 13 nodes that wait for stage 1 (statement downstream not grounded), 130 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (606)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | - | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 4 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | route |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | 4 | 1 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | 5 | 2 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` | 5 | 16 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | proof | route |
| `Sheaf.Paper.AdicCoefficientDatumCompleted` | 6 | 6 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization` | 7 | 1 | proof | route |
| `WeilConjectures.ConstructibleSheaf.Noetherian` | 8 | 2 | proof | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek` | 10 | 1 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ComparisonEtaleSliceAbelianPullback` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.LeftModuleComparisonVanishingCriterion` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.ExtensionIsoQuotientFormula` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice` | - | 1 | proof | 1 |
| `Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification` | - | 1 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.FiniteDiscreteConstructibleModel` | - | 1 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | - | 21 | proof | 1 |
| `Sheaf.Paper.InternalScalarTensorComparison` | - | 2 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | - | 3 | proof | 1 |
| `Sheaf.Paper.ShriekCoefficientIsomorphism` | - | 4 | proof | 1 |
| `Sheaf.Paper.SquareZeroPeriodicTensor` | - | 2 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.SfDerivedDirectImage` | 4 | 4 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 2 | proof | 2 |
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
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.LocalFinitePresentationInverseImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.NilpotentCoefficientDirectImageBound` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SfEtaleOriginPushforwardAmplitude` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SubfieldExtensionLocalPresentation` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.CommonStageKaroubiInverse` | - | 9 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedBelowHomTest` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.FormalExactProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbTateRootProjectionReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.ClosedSupportBoundedContinuity` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CoefficientProjectionSquare` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | - | 1 | proof | 2 |
| `Sheaf.Paper.CommonStageCalculus` | - | 8 | proof | 2 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 13 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ConstantPeriodicResolutionNonzero` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | - | 4 | proof | 2 |
| `Sheaf.Paper.ConstructibleTruncations` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedExchangeExactNormalization` | - | 3 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 2 |
| `Sheaf.Paper.EtaleDerivedDirectImageCoherence` | - | 1 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | - | 7 | proof | 2 |
| `Sheaf.Paper.EtaleWeilSheafEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.ExactScalarPeriodicResolution` | - | 6 | proof | 2 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCompactSiteCoherence` | - | 11 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.FiniteProEtalePushforwardConstructible` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteStageRationalExchangeCoherence` | - | 3 | proof | 2 |
| `Sheaf.Paper.FiniteSubextensionsDirected` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.LocalFrobeniusTrace` | - | 5 | proof | 2 |
| `Sheaf.Paper.LocalIntegralPerfectModelCohomology` | - | 1 | proof | 2 |
| `Sheaf.Paper.ModuleDerivedCompositorCoherence` | - | 4 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
| `Sheaf.Paper.PointFibreEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | - | 3 | proof | 2 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 2 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.ReductionPullbackDerivedTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 2 |
| `Sheaf.Paper.SectionDerivedPushpullNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.SectionOrdinaryOplaxNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 13 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FieldComplexCohomologySplitting` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.FixedTensorLocalizationComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatDvrScalarTensor` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatScalarCyclicResolution` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.IndFiniteFreeScalarModel` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatScalarTowerRealization` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.OneKFlatChainTranspose` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RHomColimitSourceTransport` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenFlatResolution` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomComparisonTower` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SitePerfectScalarHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.DirectImageScalarRestrictionCocycle` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleChartLeftCompositor` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison` | - | 6 | proof | 3 |
| `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` | - | 7 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.AdicBasisLimit` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ClosedEvaluationDualCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoherentCoconeNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ScalarPerfectCohomologyAndPidModels` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DirectImageRoosNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.EquivalenceAdjunctionComparison` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.EquivariantCoequalizerComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactLinearKoszulFibre` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FullyFaithfulExceptionalHomTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.InternalAbelianFiniteLimitCreation` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.JointAdjunctionModelEmbedding` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.LocalizedBasisCoefficients` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.LocallyPrescribedModulesSmall` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Monoidal.AdjunctionEquivalenceTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.MonoidalBalancingDiagrams` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares` | - | 18 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedCompositorUnitNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorSquareMateFactorization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedCompleteTriangulated` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedPullbackLinear` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedPushforwardLinear` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarCoordinateLimitCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.SectionRingLaxPushforwardCoherence` | - | 11 | proof | 3 |
| `Sheaf.CategoryTheory.SectionwiseFlatPresheafTensor` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TensorArrowMateNaturalityShifts` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TensorArrowMateRightUnit` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.UnitPowerCompleteness` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.WeakSerreBoundedThick` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.WordReconstructionCoherence` | - | 1 | proof | 3 |
| `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPerfectModelCompleteReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 3 |
| `Sheaf.Paper.AdicStratumCompletionUnit` | - | 2 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.BoundaryEtaleAdjunctionRestriction` | - | 1 | proof | 3 |
| `Sheaf.Paper.BoundaryQDefiningCompositeComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ClosedSupportedScalarComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | - | 7 | proof | 3 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedKoszulReductionRoosTriangle` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | - | 27 | proof | 3 |
| `Sheaf.Paper.CompletedRealizationDerivedCohomology` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 3 | proof | 3 |
| `Sheaf.Paper.CompletionTriangleComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.ConstantScalarStrictUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | - | 44 | proof | 3 |
| `Sheaf.Paper.DerivedNakayama` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | - | 19 | proof | 3 |
| `Sheaf.Paper.DirectImageHomEvaluationSquare` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientModelComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCompactSupportUniformTor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldLisseInternalHom` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldStratifiedGeneration` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeConstructibleScalarTransport` | - | 2 | proof | 3 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 3 |
| `Sheaf.Paper.FlatCommonQuotientReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralAmbientOperationModels` | - | 10 | proof | 3 |
| `Sheaf.Paper.IntegralCoefficientPresentationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | - | 7 | proof | 3 |
| `Sheaf.Paper.IntegralConstructibleHomSums` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCtfTriangulated` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelsExtensionClosed` | - | 1 | proof | 3 |
| `Sheaf.Paper.IsomorphismComparisonNatural` | - | 2 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 4 | proof | 3 |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | - | 1 | proof | 3 |
| `Sheaf.Paper.OpenFiniteConstructibilityInterval` | - | 1 | proof | 3 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 9 | proof | 3 |
| `Sheaf.Paper.PbcDistinguishedDiagramLifting` | - | 1 | proof | 3 |
| `Sheaf.Paper.PbcPairFunctorShiftCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.PerfectStrataUniformReductions` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointAutomorphismRestrictionNatural` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 3 |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | - | 1 | proof | 3 |
| `Sheaf.Paper.PrincipalKoszulStrictReplacement` | - | 6 | proof | 3 |
| `Sheaf.Paper.PrincipalReductionConeCalculus` | - | 2 | proof | 3 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible` | - | 3 | proof | 3 |
| `Sheaf.Paper.ProEtaleScalarMateNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.QuotientScalarComparisonDescent` | - | 2 | proof | 3 |
| `Sheaf.Paper.QuotientSystemMixedCoherence` | - | 3 | proof | 3 |
| `Sheaf.Paper.RHomColimitCohomologyLadder` | - | 4 | proof | 3 |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealWeilSheaves` | - | 2 | proof | 3 |
| `Sheaf.Paper.RealizationCompletedPull` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealizationScalarFunctor` | - | 1 | proof | 3 |
| `Sheaf.Paper.ReductionOpenEtaleOrigin` | - | 1 | proof | 3 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 3 |
| `Sheaf.Paper.RingedPullbackHomEvaluationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedTensorAdjunctionMate` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 6 | proof | 3 |
| `Sheaf.Paper.ScalarCompletionAssociator` | - | 1 | proof | 3 |
| `Sheaf.Paper.SectionExceptionalFibreCoherence` | - | 5 | proof | 3 |
| `Sheaf.Paper.SequenceSiteCompletionProjection` | - | 1 | proof | 3 |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | proof | 3 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | proof | 3 |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictPerfectRingedPullbackModel` | - | 3 | proof | 3 |
| `Sheaf.Paper.StrictQuotientExchangeUnitEquation` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedTriangleMateIdentification` | - | 1 | proof | 3 |
| `Sheaf.Paper.SystemPushforwardRestrictionTransition` | - | 1 | proof | 3 |
| `Sheaf.Paper.TwoTermReductionCohomology` | - | 1 | proof | 3 |
| `Sheaf.Paper.WeilIndSheafCategory` | - | 8 | proof | 3 |
| `Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarConjugateNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation` | - | 2 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 7 | proof | 3 |
| `Sheaf.TraceFormula.PointTransportComposition` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedTensorComplexConstraints` | 5 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 4 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 13 | 3 | proof | 4 |
| `Sheaf.Paper.PbcActualScalarPullback` | 15 | 2 | proof | 4 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatConstantScalarMono` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.BoundedProjectiveComplexDualPairing` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` | - | 6 | proof | 4 |
| `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RoosConeCalculus` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.ScalarHomChainEvaluation` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SubcategoryLeftResolution` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientFlatComplexSequence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | - | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization` | - | 5 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteConstantMapNaturality` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FlatConstructibleTensor` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.OpenSourceComposition` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalizedRingMateGraphEvaluation` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarPresentationCokernel` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | - | 6 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange` | - | 7 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AdditiveLocalizationDescent` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.AdjointEquivalenceConjugation` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.CofinalRoosRestriction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedTowerCounitProjections` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactAdjointTowerModels` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactSquareDerivedCounit` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveExactSquareComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveFiberTriangleComparison` | - | 3 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjectCokernelAction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjects.KernelStructure` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.Monoidal.UnitTensorBraiding` | - | 2 | proof | 4 |
| `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RegularScalarExtensionMultiplication` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingLocalizationSheafification` | - | 5 | proof | 4 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedTripleResolutionFormulas` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.Sites.ToposComplementFactorization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompatibleCoefficientTower` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedFiniteExchangeCoordinates` | - | 17 | proof | 4 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 4 |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedTensorUnitInsertion` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantDerivedLimitResolutionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 4 |
| `Sheaf.Paper.ContinuousCoefficientFreeRank` | - | 1 | proof | 4 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedTowerEvaluationNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleDirectImageScalarComposition` | - | 2 | proof | 4 |
| `Sheaf.Paper.EtaleOpenScalarExchange` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleSumCoefficientComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExactSectionsReductionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | - | 3 | proof | 4 |
| `Sheaf.Paper.FiniteFreeCoefficientTransport` | - | 3 | proof | 4 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 4 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | - | 5 | proof | 4 |
| `Sheaf.Paper.FlatScalarDirectImageLimitCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.FlatSingleScalarConventions` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralLineTensorCompleteness` | - | 1 | proof | 4 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | proof | 4 |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | - | 1 | proof | 4 |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | - | 1 | proof | 4 |
| `Sheaf.Paper.OpenLocalizedCounitComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.OpenScalarSiteCoherence` | - | 8 | proof | 4 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 4 |
| `Sheaf.Paper.OrdinaryPullbackStratifiedModels` | - | 10 | proof | 4 |
| `Sheaf.Paper.PbcFiniteRawScalarComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointExactDerivedModel` | - | 5 | proof | 4 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectiveTopCellAttachment` | - | 1 | proof | 4 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurAdicLineSystemBaseChange` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityFiniteOpenIntervalDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 4 |
| `Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedCoefficientPullbackComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSitePerfectProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSlicePullbackMateNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 7 | proof | 4 |
| `Sheaf.Paper.SheafTensorIdealQuotient` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratumCompletionUnitRestriction` | - | 11 | proof | 4 |
| `Sheaf.Paper.StrictHomNumeratorTranspose` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.SupportedHomCocycleNormalization` | - | 1 | proof | 4 |
| `Sheaf.ProperBaseChange.SingletonSiteModuleComparison` | - | 1 | proof | 4 |
| `Sheaf.RingTheory.ProEtale.HenselianClosedLift` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleOpenScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalAmplitude` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalBoundedSums` | - | 6 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalNeighborhoodVanishing` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.EtaleClosedComplementSets` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | 9 | 1 | proof | 5 |
| `Sheaf.RingTheory.ModuleLocalizationFilteredColimit` | 10 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.BalancedTensorChain` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.DVRProjectiveComplexMatrixModel` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus` | - | 11 | proof | 5 |
| `Sheaf.Algebra.Homology.EndomorphismFibreDoubleCone` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleStalkTotalTensorComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection` | - | 10 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SmoothAdmissibleCoordinateCover` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization` | - | 3 | proof | 5 |
| `Sheaf.CategoryTheory.Adjunction.LeftCoefficientProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.AdjunctionSquareShiftMate` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.CompositeLeftProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.CompositeRelativeTensorAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.DerivedSquareShiftOnKInjectives` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization` | - | 7 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor` | - | 5 | proof | 5 |
| `Sheaf.CategoryTheory.ExactDerivedTransformationPasting` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FiniteColimitMatrixCokernels` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FiniteRingActionLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.ModuleObjects.CoefficientDiagramRegularScalars` | - | 3 | proof | 5 |
| `Sheaf.CategoryTheory.ModuleObjects.InternalTensorCompositionUnitNormalization` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.NormalizedAdjunctionSquareTranspose` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.OpenLeftProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RoosTransitionHomotopy` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SheafTensorUnitComparison` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.Sites.ClosedComplementSiteConstruction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.TensorActionTraceContraction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.UnitAdjunctTensorAction` | - | 1 | proof | 5 |
| `Sheaf.NumberTheory.Padics.FiniteSumLattice` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | - | 23 | proof | 5 |
| `Sheaf.Paper.ConstructibleLocalizingDetermination` | - | 1 | proof | 5 |
| `Sheaf.Paper.ContinuousLatticeSum` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` | - | 1 | proof | 5 |
| `Sheaf.Paper.GeometricStalkPerfect` | - | 4 | proof | 5 |
| `Sheaf.Paper.IntegralCompositionCounitImages` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralLineReductionRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.LatticePullback` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.Paper.PuritySupportCommonInjectives` | - | 1 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackComposition` | - | 1 | proof | 5 |
| `Sheaf.Paper.SheafSliceDerivedComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | - | 1 | proof | 5 |
| `Sheaf.RingTheory.HenselianWStrictLocalInvariance` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness` | - | 6 | proof | 5 |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | - | 2 | proof | 5 |
| `Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.KFlatShortExactQuotient` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ClassicalSupportCounitIdentification` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EffectiveCartierAffineDimensionDrop` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit` | - | 5 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.CoherentRightAdjointComparisons` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.SplitFibreProjections` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.UnboundedKFlatResolution` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation` | - | 1 | proof | 6 |
| `Sheaf.FieldTheory.SepClosedAlgebrasTensorIrreducible` | - | 1 | proof | 6 |
| `Sheaf.Paper.ClassicalLocalizationTriangleTransport` | - | 1 | proof | 6 |
| `Sheaf.Paper.CommonLinePositiveScalarPowers` | - | 2 | proof | 6 |
| `Sheaf.Paper.ComparisonGlobalResolutionModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.DerivedLocalClassEdgeComparison` | - | 1 | proof | 6 |
| `Sheaf.Paper.EtaleLowerTruncationFlatModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.EtaleProEtaleCubeFlatModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.IntegralResidueClassTriangleClosure` | - | 1 | proof | 6 |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | - | 1 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarTensorTower` | - | 7 | proof | 6 |
| `Sheaf.RingTheory.HenselianSmoothAlgebraLifting` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.GeometricTwoIsoScalarPairing` | - | 1 | proof | 6 |
| `Sheaf.Topology.TopologicalBasisLiftSection` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.RingedDerivedCompositionComparison` | 15 | 1 | proof | 7 |
| `Sheaf.SixFunctors.RingedDerivedTwoIsoComparison` | 15 | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleQuotientTensorStalkCriterion` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel` | - | 11 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.SupportQuotientPairPullback` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.SemilinearTensorPresentationTransport` | - | 1 | proof | 7 |
| `Sheaf.Compactification.NagataDensityNormalizationSetup` | - | 1 | proof | 7 |
| `Sheaf.Compactification.NagataDensityNormalizationSheaves` | - | 1 | proof | 7 |
| `Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedCoefficientTensorNormalization` | - | 1 | proof | 7 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.FiniteProperProductTranspose` | - | 1 | proof | 7 |
| `Sheaf.Paper.GlobalHomEvaluationFlatLift` | - | 1 | proof | 7 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 7 |
| `Sheaf.Paper.LiftedExternalEvaluationChainModel` | - | 6 | proof | 7 |
| `Sheaf.Paper.LocalModelTorBoundDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.TAdmissibleDualizableTruncations` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SplitPerfectDualTorWindow` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology` | - | 7 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined` | - | 1 | proof | 8 |
| `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact` | - | 1 | proof | 8 |
| `Sheaf.Paper.AdmissibleScalarRealizationExact` | - | 1 | proof | 8 |
| `Sheaf.Paper.FiniteScalarPerfectRefinement` | - | 1 | proof | 8 |
| `Sheaf.Paper.ScalarPerfectDualRealization` | - | 10 | proof | 8 |
| `Sheaf.Topology.ProfiniteSectionsFiniteQuotient` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf` | - | 1 | proof | 18 |

## Stage 3: waiting for statements of dependencies (28)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | `lem-zl-constant-geometric-stalk-unit` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | 4 | 2 | `lem-sfb-integral-localization-hom-colimit` |
| `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints` | - | 4 | `lem-pur-total-tensor-signed-coherence` |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | - | 1 | `lem-sfb-scalar-hom-chain-coefficient-coherence` |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | - | 2 | `lem-sf-locally-closed-closure-adjoint-realization` |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | `lem-weil-pbc-affine-cohomology-etale-module-realization` |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | - | 4 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.CategoryTheory.NormalizedRoosShiftComparison` | - | 1 | `lem-pur-injective-tower-roos-shifts` |
| `Sheaf.CategoryTheory.SubterminalCoverModuleSES` | - | 1 | `lem-sp-subterminal-module-local-calculus` |
| `Sheaf.Paper.ClopenRoosIntegralDescent` | - | 12 | `lem-pur-finite-product-derived-tensor-calculus` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-pulled-reduction-normalization-comparison` |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | - | 1 | `lem-trf-completion-unit-strict-quotient-model` |
| `Sheaf.Paper.ExternalEvaluationTransposeNatural` | - | 1 | `lem-pur-exact-pullback-signed-comparison` |
| `Sheaf.Paper.FiniteClopenConstructibilityBounds` | - | 1 | `lem-pur-finite-product-derived-tensor-calculus` |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | - | 1 | `lem-pur-finite-open-product-swap` |
| `Sheaf.Paper.IntegralModelOpenClosedPieces` | - | 1 | `lem-weil-pbc-proetale-closed-underived-projection` |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | - | 1 | `lem-trf-point-transport-strict-quotient` |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | `lem-pd-section-derived-open-adjunction-normalization` |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | `lem-pur-injective-tower-roos-shifts` |
| `Sheaf.Paper.PurityGeneralAdmissibility` | - | 1 | `lem-pur-affine-chart-exceptional-identification` |
| `Sheaf.Paper.QcqsProperHullTailBound` | - | 1 | `lem-sfb-qcqs-proper-serre-heart-bound` |
| `Sheaf.Paper.SectionReesBaseChangeEtale` | - | 6 | `lem-trf-section-rees-noetherian-geometry` |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | - | 1 | `lem-weil-pbc-augmented-diagram-projection-mate` |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | - | 1 | `lem-sfb-continuous-algcl-open-finiteness` |
| `Sheaf.SixFunctors.AdmissibleTensorConstructibility` | - | 1 | `lem-sfb-finite-flat-constructible-total-tensor` |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | - | 1 | `lem-sfb-ordinary-proetale-direct-image-plus-comparison` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `lem-sfb-condensed-bounded-hom-continuity` |

## Stage 3: held for an open upstream PR (18)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
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
