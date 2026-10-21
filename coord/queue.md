# Work queue

295 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (11 clusters, 1358 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 63, stage 3 211 items.

## Stage 1: nodes to split (127)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-qbar-condensed-two-colimit` | 0 | rests_on_sorry |
| `prop-weil-pbc-scalar-extension` | 1 | none |
| `lem-pd-monoidal-adjunction-equivalence-transport` | 3 | none |
| `lem-pd-ringed-direct-image-pairing-lax` | 3 | none |
| `lem-pd-ringed-tensor-adjunction-mate` | 3 | none |
| `lem-pur-finite-coefficient-adjoint-comparisons` | 3 | none |
| `lem-weil-pbc-bounded-complex-triangulated-devissage` | 3 | none |
| `lem-weil-pbc-flat-scalar-restriction-kflat` | 3 | none |
| `lem-weil-pbc-ringed-common-quotient-pullback-comparison` | 3 | none |
| `lem-weil-pbc-strict-perfect-ringed-pullback-model` | 3 | none |
| `lem-weil-pbc-finite-etale-cover-cech-stage-comparison` | 4 | none |
| `lem-weil-pbc-realization-adjoint-comparisons` | 4 | none |
| `lemma-weil-pbc-completed-pullback-reduction` | 4 | none |
| `lem-weil-pbc-discrete-exchange-site-comparison` | 5 | none |
| `lem-weil-pbc-heart-test-bounded-below` | 5 | none |
| `lem-sbc-koszul-fibre-linear-descent` | 6 | none |
| `lem-sbc-reflected-compositor-unit-normalization` | 6 | none |
| `lem-sbc-reflector-adjunction-unit-formulas` | 6 | none |
| `lem-sbc-reflector-square-mate-factorization` | 6 | none |
| `lem-sbc-strict-quotient-exchange-unit-equation` | 6 | none |
| `lem-sbc-unbounded-exact-adjunction-square` | 6 | none |
| `lem-weil-pbc-lisse-e-constructible-integral-lattice` | 9 | none |
| `lem-weil-pbc-smooth-curve-etale-structure-direct-images` | 16 | none |
| `lem-weil-pbc-coherent-affine-base-change-edge-naturality` | 17 | none |
| `sk-prop-sfb-qlbar-colimit-x` | 1000 | rests_on_sorry |
| `lem-weil-finite-free-completed-scalar-comparison` | 1001 | none |
| `lem-sf-compact-support-restriction-of-scalars` | 1002 | none |
| `lem-sf-integral-compact-support-constructible` | 1002 | none |
| `lem-weil-compact-support-reduction-tower-functor` | 1002 | none |
| `lem-pur-additive-localization-descent` | 1003 | none |
| `lem-pur-compatible-coefficient-tower` | 1003 | none |
| `lem-pur-strict-roos-homotopy-functor` | 1003 | none |
| `lem-pur-diagram-ring-restriction-pushforward` | 1005 | none |
| `lem-pur-roos-intrinsic-completeness-equivalence` | 1005 | none |
| `def-weil-common-stage-derived-direct-image` | 1016 | none |
| `det-def-sp-tate-twist-locally-free` | 2000 | none |
| `lem-sf-integral-direct-image-constructible` | 2002 | none |
| `det-sf-comp-coherence-cocycle` | 2003 | none |
| `lem-cbc-completed-extension-zero-comparison` | 2003 | none |
| `det-sf-existence-brown` | 2005 | none |
| `lem-cbc-derived-constant-tower-normalization` | 2005 | none |
| `lem-cbc-derived-finite-quotient-coherence` | 2005 | none |
| `lem-pe-ringed-site-derived-evaluation-slice` | 2005 | none |
| `lem-pur-adic-line-system-base-change` | 2005 | none |
| `lem-pur-etale-compact-scalar-coherence` | 2005 | none |
| `lem-pur-signed-line-derived-base-change` | 2005 | none |
| `lem-pur-site-representable-algebraic-pullback` | 2005 | none |
| `lem-pur-torsion-line-system-base-change` | 2005 | none |
| `lem-fix-operation-reduction` | 3002 | none |
| `lem-coef-derived-system-evaluation-calculus` | 5002 | none |
| `lem-fix-compact-support-coefficient-change` | 5003 | none |
| `lem-sf-bounded-below-hom-test` | 5005 | none |
| `lem-sfb-constant-scalar-geometric-adjunctions` | 5005 | none |
| `lem-sfb-constant-scalar-restriction-tensor` | 5005 | none |
| `lem-sfb-ring-isomorphism-tensor-transport` | 5005 | none |
| `lem-sfb-scalar-normalized-constant-models` | 5005 | none |
| `det-prop-sfb-cartesian-coefficients-finite-free` | - | none |
| `lem-sfb-coefficient-push-filtered-legs` | - | none |
| `lem-sfb-dc-upper-star-preserves` | - | none |
| `lem-sfb-derived-exchange-exact-normalization` | - | none |
| `lem-sfb-subfield-push-iso` | - | sorry_here |
| `det-sp-scalar-extension-functor` | - | none |
| `lem-pur-finite-free-completion-exchange` | - | none |
| `lem-pur-finite-free-completion-exchange-coherence` | - | none |
| `lem-pur-integral-ambient-operation-models` | - | none |
| `lem-pur-scalar-hom-comparison-tower` | - | none |
| `lem-sfb-closed-supported-scalar-comparison` | - | none |
| `lem-sfb-coextension-iso-evaluation-formula` | - | none |
| `lem-sfb-equivalence-square-inverse-mate-coherence` | - | none |
| `lem-sfb-exact-open-closed-unbounded-calculus` | - | none |
| `lem-sfb-extension-iso-quotient-formula` | - | none |
| `lem-sfb-filtered-colimit-flat-module-sheaves` | - | none |
| `lem-sfb-finite-discrete-constructible-model` | - | none |
| `lem-sfb-integral-ambient-tower-comparison` | - | none |
| `lem-sfb-integral-constructible-completion-bridge` | - | none |
| `lem-sfb-integral-quotient-direct-image-comparison` | - | none |
| `lem-sfb-integral-quotient-exchange-comparison` | - | none |
| `lem-sfb-integral-quotient-projection-comparison` | - | none |
| `lem-sfb-internal-scalar-extension-section-test` | - | none |
| `lem-sfb-internal-section-scalar-adjunction` | - | none |
| `lem-sfb-kflat-scalar-comparison-normalization` | - | none |
| `lem-sfb-lfp-scalar-isomorphism` | - | none |
| `lem-sfb-localized-direct-image-comparison` | - | none |
| `lem-sfb-normalized-immersion-comparison-coherence` | - | none |
| `lem-sfb-normed-coefficient-realization` | - | none |
| `lem-sfb-open-module-restriction-identities` | - | none |
| `lem-sfb-open-scalar-conjugate-normalization` | - | none |
| `lem-sfb-qlbar-direct-image-comparison` | - | none |
| `lem-sfb-section-ring-lax-pushforward-coherence` | - | none |
| `sk-def-pe-derived-completion` | - | none |
| `sk-lem-integral-models` | - | none |
| `sk-prop-sfb-cartesian-coefficients` | - | rests_on_sorry |
| `lem-pe-finite-scalar-restriction-constructible` | - | none |
| `lem-sfb-modobj-forget-creates` | - | none |
| `lem-sfb-scalar-coordinate-limit-criterion` | - | none |
| `lem-sfb-scalar-presentation-cokernel` | - | none |
| `lem-sfb-stratified-local-cohomological-bounds` | - | none |
| `lem-sfb-tor-interval-local-detection` | - | none |
| `lem-sp-chart-counit-scalar-transport` | - | none |
| `lem-sp-chart-finite-ring-adjunction` | - | none |
| `lem-sp-chart-left-scalar-normalization` | - | none |
| `lem-sp-etale-ctf-chart-domain` | - | none |
| `lem-sp-open-exceptional-scalar-locality` | - | none |
| `lem-sp-open-proetale-counit-scalar` | - | none |
| `lem-sp-smooth-admissible-coordinate-cover` | - | none |
| `lem-sf-semilinear-alpha-pullback` | - | none |
| `lem-sf-semilinear-compositor-coherence` | - | none |
| `lem-sf-semilinear-scalar-derived-comparison` | - | none |
| `lem-sf-semilinear-scalar-ordinary-comparison` | - | none |
| `lem-sfb-constructible-local-tor-etale-origin` | - | none |
| `lem-sfb-lattice-pullback` | - | none |
| `lem-sfb-local-integral-perfect-model-cohomology` | - | none |
| `lem-sfb-module-object-ringed-site-derived-comparison` | - | none |
| `lem-sfb-rational-derived-scalar-invertible` | - | none |
| `det-brown-hypotheses-small` | - | none |
| `lem-sfb-base-coefficient-condensed-identification` | - | none |
| `lem-sfb-shriek-coefficient-isomorphism` | - | none |
| `lem-sp-exact-derived-transformation-pasting` | - | none |
| `lem-sp-ordinary-horizontal-pasting-transport` | - | none |
| `lem-sp-ordinary-vertical-pasting-transport` | - | none |
| `lem-sp-varying-ring-cartesian-comparison-lift-relabelling` | - | none |
| `lem-sp-varying-ring-cartesian-lift-pullback-equivalence` | - | none |
| `lem-sp-varying-ring-open-unit-coherence` | - | none |
| `lem-sp-varying-ring-pullback-unit-coherence` | - | none |
| `lem-sfb-finite-proper-classical-neighborhood-vanishing` | - | none |
| `lem-sp-etale-derived-chain-transpose` | - | none |
| `lem-sp-flat-coefficient-chain-transpose` | - | none |

## Stage 2: nodes to state (58)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `lem-weil-pbc-realization-scalar-functor` | 1 | state | 3 |
| `lem-weil-pbc-constant-tower-pushforward-normalization` | 1 | state | 1 |
| `lem-weil-pbc-finite-intersection-limit-compatibility` | 1 | state | 1 |
| `lem-weil-pbc-kflat-fixed-tensor-triangulated` | 1 | state | 1 |
| `lem-weil-pbc-reduction-pullback-derived-tower` | 1 | state | 1 |
| `lem-cbc-derived-tower-evaluation-normalization` | 1 | state | 0 |
| `lem-cbc-finite-constant-map-naturality` | 1 | state | 0 |
| `lem-cbc-open-localized-counit-comparison` | 1 | state | 0 |
| `lem-pe-comparison-etale-slice-abelian-pullback` | 1 | state | 0 |
| `lem-pe-left-module-comparison-vanishing-criterion` | 1 | state | 0 |
| `lem-pe-profinite-sections-finite-quotient` | 1 | state | 0 |
| `lem-pe-scalar-cone-tensor-model` | 1 | state | 0 |
| `lem-pe-successive-quotient-linear-triangle` | 1 | state | 0 |
| `lem-pur-ringed-derived-composition-cocycle` | 1 | state | 0 |
| `lem-sf-adjunct-conjugate-open-factor` | 1 | state | 0 |
| `lem-sf-etale-chart-adjoint-comparison` | 1 | state | 0 |
| `lem-sf-localizing-hom-test` | 1 | state | 0 |
| `lem-sf-normalized-derived-comparison-composition` | 1 | state | 0 |
| `lem-sf-semilinear-clopen-unit-projector` | 1 | state | 0 |
| `lem-sfb-adic-perfect-model-complete-reduction` | 1 | state | 0 |
| `lem-sfb-adic-stratum-completion-unit` | 1 | state | 0 |
| `lem-sfb-bounded-bifunctor-devissage` | 1 | state | 0 |
| `lem-sfb-closed-support-bounded-continuity` | 1 | state | 0 |
| `lem-sfb-constructible-cocone-ambient-realization` | 1 | state | 0 |
| `lem-sfb-continuous-lattice-sum` | 1 | state | 0 |
| `lem-sfb-finite-etale-trace-image` | 1 | state | 0 |
| `lem-sfb-finite-field-proetale-direct-image` | 1 | state | 0 |
| `lem-sfb-finite-field-stratified-generation` | 1 | state | 0 |
| `lem-sfb-finite-sum-lattice` | 1 | state | 0 |
| `lem-sfb-flat-dvr-scalar-tensor` | 1 | state | 0 |
| `lem-sfb-flat-scalar-cyclic-resolution` | 1 | state | 0 |
| `lem-sfb-grothendieck-sheafification` | 1 | state | 0 |
| `lem-sfb-hom-flat-evaluation-roof` | 1 | state | 0 |
| `lem-sfb-hom-kflat-chain-transpose` | 1 | state | 0 |
| `lem-sfb-hom-scalar-chain-identification` | 1 | state | 0 |
| `lem-sfb-integral-derived-extension-comparison` | 1 | state | 0 |
| `lem-sfb-internal-hom-localization-comparison` | 1 | state | 0 |
| `lem-sfb-locally-free-derived-scalars` | 1 | state | 0 |
| `lem-sfb-modobj-restriction-finite-exact` | 1 | state | 0 |
| `lem-sfb-projection-comparison-etale-proetale` | 1 | state | 0 |
| `lem-sfb-rhom-continuity-triangle-closure` | 1 | state | 0 |
| `lem-sfb-ringed-complete-triangulated` | 1 | state | 0 |
| `lem-sfb-scalar-inverse-image-tower-diagram` | 1 | state | 0 |
| `lem-sfb-scalar-model-finite-flat-resolution` | 1 | state | 0 |
| `lem-sfb-square-zero-periodic-tensor` | 1 | state | 0 |
| `lem-sfb-subobject-inclusion-cokernel` | 1 | state | 0 |
| `lem-sp-etale-sum-coefficient-computation` | 1 | state | 0 |
| `lem-sp-finite-compact-site-coherence` | 1 | state | 0 |
| `lem-sp-finite-ring-action-local-constancy` | 1 | state | 0 |
| `lem-sp-open-scalar-site-coherence` | 1 | state | 0 |
| `lem-weil-pbc-direct-image-roos-normalization` | 1 | state | 0 |
| `lem-weil-pbc-flat-common-quotient-reduction-tower` | 1 | state | 0 |
| `lem-weil-pbc-flat-constant-tensor-pro-zero-cones` | 1 | state | 0 |
| `lem-weil-pbc-formal-exact-projection-mate` | 1 | state | 0 |
| `lem-weil-pbc-ringed-slice-comparisons-shift` | 1 | state | 0 |
| `lem-weil-pbc-stratum-completion-unit-restriction` | 1 | state | 0 |
| `lem-sfb-finite-classical-localizing` | 2 | state | 0 |
| `lem-sfb-subfield-extension-local-presentation` | 2 | state | 0 |

Not open yet: 300 nodes that below a finished node, not needed, 91 nodes that wait for a statement dependency (bottom-up), 98 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (89)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 11 | 1 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | - | 4 | proof | route |
| `Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.CohomologyTorInterval` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | - | 2 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | - | 2 | proof | 1 |
| `Sheaf.Paper.ProEtaleConstructibleExactClosure` | - | 1 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | - | 1 | proof | 1 |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.EtaleStalkTorTest` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | - | 15 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | - | 3 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 7 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 4 | proof | 2 |
| `Sheaf.CategoryTheory.SheafificationTensorLocalIso` | 10 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleAmbientOperationsScalarLinearity` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProperGeometricFibreCohomologicalBound` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.Sites.ProperGeometricFibreTorsionBound` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FilteredTwoColimitCharacterization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FilteredTwoColimitModel` | - | 15 | proof | 3 |
| `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.MonoidalFiniteFreeTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RationalizationLocalizationHomCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | - | 4 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarUnitEqualityDetection` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` | - | 1 | proof | 3 |
| `Sheaf.FieldTheory.CondensedSubfieldBasis` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.DerivedNakayamaResolution` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 3 | proof | 3 |
| `Sheaf.Paper.FiniteFieldStratifiedPerfectModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteSubextensionsDirected` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | - | 2 | proof | 3 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | - | 5 | proof | 3 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedSlicePullbackMateNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 9 | proof | 3 |
| `Sheaf.Algebra.Homology.RoosConeCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.AffineRootsRepresentability` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactDerivedComposition` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactFaithfulTorsion` | - | 5 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | - | 3 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 2 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation` | - | 1 | proof | 5 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarCounitTransposes` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | - | 9 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.Paper.DivisibleExtensionDerivedReduction` | - | 5 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |

## Stage 3: waiting for statements of dependencies (31)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation` | - | 1 | `lem-sfb-grothendieck-sheafification` |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | - | 1 | `lem-sfb-scalar-presentation-cokernel` |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | `lem-weil-pbc-coherent-affine-base-change-edge-naturality` |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | `lem-cbc-finite-constant-map-naturality` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-adic-line-system-base-change` |
| `Sheaf.Paper.CoefficientHeartFiltration` | - | 1 | `lem-sfb-subobject-inclusion-cokernel` |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | `lem-pur-diagram-ring-restriction-pushforward` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | `lem-pe-completion-triangle-comparison` |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | `lem-sp-proetale-scalar-tensor-normalization` |
| `Sheaf.Paper.DlConstructibleFibresExact` | - | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | `lem-sfb-finite-field-proetale-direct-image` |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | `lem-sfb-projection-comparison-etale-proetale` |
| `Sheaf.Paper.FiniteProperLocalizing` | - | 3 | `lem-sfb-finite-classical-localizing` |
| `Sheaf.Paper.IntegralCriterionReductions` | - | 8 | `lem-pe-finite-coefficient-model-comparison` |
| `Sheaf.Paper.IntegralModelsOperations` | - | 1 | `lem-sfb-scalar-model-immersion-extension` |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | `lem-pur-finite-free-completion-exchange` |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | - | 1 | `lem-sfb-scalar-model-finite-flat-resolution` |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | `lem-pd-section-derived-pushpull-normalization` |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | - | 3 | `lem-pd-ringed-direct-image-pairing-lax` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | `lem-sbc-koszul-fibre-linear-descent` |
| `Sheaf.Paper.StratifiedLattice` | - | 1 | `lem-sfb-lattice-pullback` |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | - | 1 | `lem-sf-normalized-derived-comparison-composition` |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | `lem-sp-finite-ring-action-local-constancy` |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | `lem-sfb-finite-proper-classical-neighborhood-vanishing` |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | `lem-sfb-lattice-subquotient-filtration` |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | `lem-sfb-closed-supported-scalar-comparison` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | - | 2 | `lem-sfb-integral-derived-extension-comparison` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `lem-sfb-condensed-bounded-hom-continuity` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | - | 2 | `lem-sfb-finite-discrete-constructible-model` |

## Stage 3: held for an open upstream PR (18)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
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
