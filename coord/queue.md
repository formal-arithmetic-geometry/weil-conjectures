# Work queue

623 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (11 clusters, 1069 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.CategoryTheory.MappedSmartTruncationTower` | 1 |  | error: Sheaf/CategoryTheory/MappedSmartTruncationTower.lean:5:0: error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed, environment already con |
| `Sheaf.Algebra.Homology.IntegralBoundedKunnethExact` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 39, stage 3 90 items.

## Stage 1: nodes to split (325)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-qbar-condensed-two-colimit` | 0 | none |
| `lem-pd-module-ringed-topos-derived-comparison` | 1 | none |
| `prop-weil-pbc-scalar-extension` | 1 | none |
| `lem-weil-pbc-integral-stratified-perfect-characterization` | 2 | none |
| `prop-weil-pbc-descent-functors` | 2 | none |
| `lem-weil-pbc-direct-image-roos-normalization` | 3 | none |
| `lem-weil-pbc-formal-exact-projection-mate` | 3 | none |
| `lem-weil-pbc-kflat-fixed-tensor-triangulated` | 3 | none |
| `lem-pur-etale-affine-projection-coefficient-mate` | 4 | none |
| `lem-pur-etale-closed-chart-exceptional-preservation` | 4 | none |
| `lem-pur-etale-finite-tor-direct-image-coefficients` | 4 | none |
| `lem-pur-etale-injective-support-sequence` | 4 | none |
| `lem-pur-etale-kflat-support-comparison` | 4 | none |
| `lem-pur-local-field-coefficient-stages` | 4 | none |
| `lem-pur-supported-triangle-mate-identification` | 4 | none |
| `lem-weil-pbc-ordered-exchange-coefficient-comparison` | 4 | none |
| `lem-weil-pbc-ringed-slice-comparisons-shift` | 4 | none |
| `lem-weil-pbc-ringed-slice-pullback-mate-normalization` | 4 | none |
| `lem-weil-pbc-scalar-localization-sheaf-exact` | 4 | none |
| `lem-weil-pbc-tower-derived-evaluation-normalization` | 4 | none |
| `lem-weil-pbc-flat-coefficient-reduction-adjunct` | 5 | none |
| `lem-weil-pbc-flat-scalar-koszul-tower-comparison` | 5 | none |
| `lem-weil-pbc-pulled-reduction-normalization-comparison` | 5 | none |
| `lem-weil-pbc-pulled-reduction-strict-tower-comparison` | 5 | none |
| `sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch` | 5 | none |
| `sk-thm-purity-transport` | 5 | none |
| `lem-pur-normalized-reconstruction-adjunction-calculus` | 6 | none |
| `lem-weil-pbc-flat-common-quotient-reduction-tower` | 6 | none |
| `lem-sbc-ringed-site-perfect-projection-formula` | 7 | none |
| `lem-weil-pbc-integral-constructible-hom-sums` | 10 | none |
| `lem-weil-pbc-integral-model-open-closed-pieces` | 10 | none |
| `lem-weil-pbc-integral-models-extension-closed` | 10 | none |
| `lem-weil-pbc-lisse-lattice-reduced-open` | 10 | none |
| `lem-weil-pbc-affine-cohomology-etale-module-realization` | 17 | none |
| `lem-weil-pbc-flat-curve-derived-structure-model` | 17 | none |
| `lem-weil-pbc-derived-pullback-top-cohomology` | 18 | none |
| `lem-weil-pbc-top-base-change-presheaf` | 18 | none |
| `lem-sfb-qlbar-point-abelian-colimit` | 1001 | none |
| `lem-weil-compact-support-representative-independence` | 1002 | none |
| `lem-pur-adic-basis-limit` | 1003 | none |
| `lem-pur-completed-operation-tower-substitution` | 1003 | none |
| `lem-pur-finite-free-quotient-completion` | 1003 | none |
| `lem-pur-integral-coherence-tower` | 1003 | none |
| `lem-pur-quotient-scalar-comparison-descent` | 1003 | none |
| `lem-pur-regular-quotient-completion-unit` | 1003 | none |
| `lem-pur-ringed-derived-pullback-linear` | 1003 | none |
| `lem-pur-ringed-derived-pushforward-linear` | 1003 | none |
| `lem-pur-sequence-site-completion-projection` | 1003 | none |
| `lem-pur-sequence-site-open-extension` | 1003 | none |
| `lem-pur-system-pushforward-restriction-transition` | 1003 | none |
| `lem-pur-unit-power-completeness` | 1003 | none |
| `lem-sf-direct-image-scalar-restriction-cocycle` | 1003 | none |
| `lem-sf-open-extension-scalar-restriction-coherence` | 1003 | none |
| `lem-pur-ringed-derived-composition-cocycle` | 1004 | none |
| `lem-pur-scalar-extension-tower-coherence` | 1004 | none |
| `lem-sf-reduction-flat-model` | 1004 | none |
| `lem-pur-composite-integration-counit` | 1005 | none |
| `lem-pur-degree-zero-derived-map-gluing` | 1005 | none |
| `lem-pur-finite-clopen-derived-decomposition` | 1005 | none |
| `lem-pur-finite-projection-action-laws` | 1005 | none |
| `lem-pur-proetale-inverse-image-tensor-comparison` | 1005 | none |
| `lem-pur-projection-formula-coefficient-coherence` | 1005 | none |
| `lem-weil-integral-ctf-triangulated` | 1006 | none |
| `lem-pur-etale-iso-descent` | 1007 | none |
| `lem-pur-finite-etale-dualizing-normalization` | 1007 | none |
| `lem-sfb-base-change-identity-open-restriction` | 1007 | none |
| `lem-pur-retracted-support-localization-comparison` | 1008 | none |
| `lem-sf-fixed-pair-adjunction-lift` | 1017 | none |
| `lem-pur-completed-line-tensor-coherence` | 2001 | none |
| `lem-pur-integral-line-reduction-restriction` | 2001 | none |
| `lem-pur-line-unbounded-derived-tensor` | 2001 | none |
| `def-wf-tensor-product` | 2003 | none |
| `lem-sf-etale-origin-pushforward-amplitude` | 2003 | none |
| `lem-sf-finite-proetale-pushforward-constructible` | 2003 | none |
| `lem-sf-nilpotent-coefficient-direct-image-bound` | 2003 | none |
| `lem-weil-constant-coefficient-objects-constructible` | 2003 | none |
| `lem-amb-finite-tate-site-descent` | 2004 | none |
| `lem-cbc-completed-ring-strict-finite-exchange` | 2004 | none |
| `lem-cbc-exact-linear-koszul-fiber` | 2004 | none |
| `lem-cbc-ringed-open-flat-resolution` | 2004 | none |
| `lem-cbc-ringed-open-strict-reduction` | 2004 | none |
| `lem-sfb-identity-open-derived-restriction` | 2004 | none |
| `lem-sfb-module-derived-compositor-coherence` | 2004 | none |
| `lem-sfb-normalized-open-refinement-coherence` | 2004 | none |
| `lem-sfb-qcqs-proper-open-boundary-vanishing` | 2004 | none |
| `lem-weil-integral-twist-base-change` | 2004 | none |
| `lem-fix-residue-lisse-projective-models` | 2005 | none |
| `lem-pur-etale-compact-scalar-coherence` | 2005 | none |
| `lem-pur-integral-twist-line-inverse-image` | 2005 | none |
| `prop-every-iterate-trace` | 2005 | none |
| `sk-def-sf-admissible` | 2005 | none |
| `lem-cbc-complete-proetale-strict-tower-realization` | 2006 | none |
| `lem-cbc-finite-extension-reduction-cone-bound` | 2006 | none |
| `lem-sf-cbc-compact-support-composition-limit` | 2006 | none |
| `lem-sf-cbc-extension-zero-completion` | 2006 | none |
| `lem-sf-complete-residue-cohomology-bounds` | 2006 | none |
| `lem-sfb-coherent-right-adjoint-comparisons` | 2006 | none |
| `lem-pur-support-comparison-boundary` | 2007 | none |
| `lem-pur-supported-hom-pullback` | 2007 | none |
| `lem-pur-finite-forward-product-symmetry` | 2008 | none |
| `lem-pur-shifted-tensor-morphism-calculus` | 2008 | none |
| `lem-pur-site-comparison-edge-section` | 2008 | none |
| `lem-pur-support-quotient-product` | 2008 | none |
| `lem-weil-integral-twist-scalar-coherence` | 2008 | none |
| `lem-pur-relative-support-coordinate-model` | 2009 | none |
| `lem-pur-external-rhom-cone-pairing` | 2011 | none |
| `thm-pur-rank-one-thom` | 2020 | none |
| `lem-sfb-finite-upper-star-braided` | 3001 | none |
| `lem-fix-compactification-completed-realization` | 3003 | none |
| `lem-fix-scalar-completion-associator` | 3003 | none |
| `lem-fix-site-perfect-scalar-hom` | 3003 | none |
| `lemma-nagata-open-immersion-qc-over-separated-target` | 3003 | none |
| `def-kun-separably-closed` | 3004 | none |
| `lem-trf-integral-pullback-comparison-realization` | 3004 | none |
| `lem-weil-isomorphism-derived-pullback-comparison-normalization` | 3004 | none |
| `lemma-nagata-finite-type-to-separated-target` | 3004 | none |
| `lemma-nagata-immersion-open-in-scheme-image` | 3004 | none |
| `def-nagata-scheme-image-factor` | 3005 | none |
| `def-nagata-scheme-theoretic-closure` | 3005 | none |
| `def-nagata-scheme-theoretic-image` | 3005 | none |
| `lem-pur-dnc-section-geometry` | 3005 | none |
| `lemma-nagata-scheme-image-ideal-qc` | 3005 | none |
| `lemma-nagata-scheme-image-of-closed-immersion` | 3005 | none |
| `def-nagata-affine-proj` | 3006 | none |
| `def-nagata-homogeneous-localization-degree-zero` | 3006 | none |
| `lem-trf-integral-point-transport-tower-powers` | 3008 | none |
| `lem-trf-integral-inverse-image-comparison-composition` | 3009 | none |
| `sk-thm-picard-rr` | 3014 | none |
| `sk-thm-picard-duality` | 3015 | none |
| `prop-nagata-proj-standard-open` | 3023 | none |
| `lem-sfb-ringed-site-duality-maps` | 4003 | none |
| `lem-trf-finite-ring-section-deformation` | 4003 | none |
| `lem-sfb-ringed-site-strict-perfect-hom` | 4004 | none |
| `lem-trf-integral-point-transport-tower-realization` | 4004 | none |
| `prop-functor-package` | 4005 | none |
| `def-pur-scheme-geometric-frobenius` | 4006 | none |
| `lem-sfb-admissible-direct-image` | 4006 | none |
| `lem-sfb-admissible-tensor-constructibility` | 4006 | none |
| `def-pod-perfect-derived-pairing` | 4007 | none |
| `lem-sfb-internal-hom-dual-constructible-models` | 4007 | none |
| `lem-sfb-internal-hom-dual-tor-amplitude` | 4007 | none |
| `lem-trf-point-transport-composition` | 4008 | none |
| `lem-coef-closed-adjunction-enriched-isomorphism` | 5003 | none |
| `lem-coef-enriched-sequence-projection-formula` | 5003 | none |
| `lem-coef-integral-compact-support` | 5003 | none |
| `lem-coef-ringed-pullback-hom-evaluation-comparison` | 5003 | none |
| `lem-coef-sequence-global-sections-evaluation` | 5003 | none |
| `lem-coef-sequence-projection-derived-adjunction` | 5003 | none |
| `lem-coef-sequence-pushforward-limit-projections` | 5003 | none |
| `lem-coef-sequence-sections-limit-comparison` | 5003 | none |
| `lem-sf-point-fibre-derived-tensor` | 5003 | none |
| `lem-coef-tower-coaugmentation` | 5004 | none |
| `lem-weil-frobenius-point-transport-natural` | 5004 | none |
| `cor-cbc-proper-coincidence` | 5005 | none |
| `cor-coef-integral-internal-hom` | 5005 | none |
| `lem-coef-internal-adjunction-pairing-change` | 5005 | none |
| `lem-coef-site-closed-counit-transport` | 5005 | none |
| `lem-sf-etale-chart-adjoint-comparison` | 5005 | none |
| `lem-sf-etale-stalk-tor-test` | 5005 | none |
| `lem-weil-finite-duality-locally-closed-comparison` | 5005 | none |
| `lem-weil-isomorphism-comparison-scalar-extension` | 5005 | none |
| `sk-def-sf-kv-maps` | 5005 | none |
| `thm-pur-general-admissibility` | 5005 | none |
| `lem-fix-site-open-exchange-square` | 5006 | none |
| `lem-sf-pf-open-factor-coherence` | 5006 | none |
| `lem-weil-specified-pullback-comparison-alpha` | 5006 | none |
| `lem-trf-weakly-etale-between-objects` | 5007 | none |
| `lem-weil-boundary-dualizing-composition` | 5007 | none |
| `lem-weil-boundary-proetale-projection-comparison` | 5007 | none |
| `lem-weil-boundary-proetale-q-compatibility` | 5007 | none |
| `lem-kun-0f1m` | 5010 | none |
| `sk-lem-picard-cech-computes` | 5017 | none |
| `lem-sf-immersion-completed-pullback-comparison` | 6004 | none |
| `lem-trf-site-derived-tensor-restriction` | 6004 | none |
| `sk-thm-picard-pn` | 6016 | none |
| `sk-thm-picard-cech` | 6018 | none |
| `sk-lem-regular-smooth` | 7007 | none |
| `def-nagata-relative-affine-space` | 7009 | none |
| `sk-lem-nagata-sketch-dense-valuative` | 7019 | none |
| `lemma-nagata-local-domain-valuation-dominates` | 7020 | none |
| `lemma-nagata-projective-target-local` | 8022 | none |
| `sk-def-sfb-dc-setting` | - | none |
| `lem-sfb-dc-upper-star-preserves` | - | none |
| `def-sfb-left-derived-exact` | - | none |
| `det-lem-int-tensor-pullback` | - | none |
| `lem-sf-integral-open-reduction-comparison` | - | none |
| `lem-sfb-condensed-subfield-basis` | - | none |
| `lem-sfb-dc-hom-small-coefficients` | - | none |
| `lem-sfb-flat-scalar-cyclic-resolution` | - | none |
| `lem-sfb-internal-extension-inverse-image` | - | none |
| `lem-sfb-localized-basis-coefficients` | - | none |
| `lem-sfb-locally-free-derived-scalars` | - | none |
| `lem-sp-ringed-topos-binary-descent` | - | none |
| `lem-weil-point-sections-scalar-extension` | - | none |
| `sk-def-cohfamily` | - | none |
| `sk-lem-integral-models` | - | none |
| `sk-lem-sp-tower` | - | none |
| `sk-prop-sfb-cartesian-coefficients` | - | none |
| `def-sfb-left-derived-functor` | - | none |
| `def-weil-complex-weights` | - | none |
| `lem-pe-kflat-scalar-tower-realization` | - | none |
| `lem-pe-successive-quotient-linear-triangle` | - | none |
| `lem-pe-two-term-reduction-cohomology` | - | none |
| `lem-sfb-cohomology-tor-interval` | - | none |
| `lem-sfb-dc-hom-filtered-colimit` | - | none |
| `lem-sfb-internal-hom-localization-comparison` | - | none |
| `lem-sfb-scalar-matrix-inverse-image` | - | none |
| `lem-sfb-scalar-model-finite-flat-resolution` | - | none |
| `lem-sfb-square-zero-periodic-tensor` | - | none |
| `lem-sp-etale-ctf-chart-domain` | - | none |
| `lem-sp-restricted-scalar-cohomology-local-constancy` | - | none |
| `lem-sp-signed-tate-coefficient-exponent-normalization` | - | none |
| `prop-weil-operations` | - | none |
| `def-nagata-final-basechanged-compactification` | - | none |
| `def-nagata-final-fp-envelope` | - | none |
| `def-nagata-scheme-image-comparison` | - | none |
| `def-weil-punctual-weights` | - | none |
| `det-ctf-finite-proper-localizing` | - | none |
| `det-lem-int-integral-heart-local-model` | - | none |
| `det-lem-int-integral-heart-triangulated` | - | none |
| `lem-a1-integral-pullback-completed-comparison` | - | none |
| `lem-pe-roos-cone-calculus` | - | none |
| `lem-sfb-constructible-cocone-ambient-realization` | - | none |
| `lem-sfb-continuous-lattice-sum` | - | none |
| `lem-sfb-divisible-extension-derived-reduction` | - | none |
| `lem-sfb-etale-proetale-scalar-pullback-cube` | - | none |
| `lem-sfb-finite-field-closed-support` | - | none |
| `lem-sfb-finite-field-proetale-direct-image` | - | none |
| `lem-sfb-hom-flat-evaluation-roof` | - | none |
| `lem-sfb-hom-scalar-chain-identification` | - | none |
| `lem-sfb-rhom-continuity-triangle-closure` | - | none |
| `lem-tw-ordinary-completed-integral-pullback` | - | none |
| `lem-zl-constant-sheaf-weight-zero` | - | none |
| `lemma-nagata-final-noetherian-compactification` | - | none |
| `sk-def-perfect` | - | none |
| `def-nagata-extended-ideal` | - | none |
| `def-nagata-final-noetherian-compactification` | - | none |
| `def-nagata-immersion-into-fp-model` | - | none |
| `def-nagata-immersion-shrink-to-closed` | - | none |
| `def-nagata-rees-algebra` | - | none |
| `def-trf-trace-class-source` | - | none |
| `i-relative-frob` | - | none |
| `lem-pur-compact-support-completed-projection-coherence` | - | none |
| `lem-sfb-coefficient-cocone-comparison-agreement` | - | none |
| `lem-sfb-etale-derived-tensor-stalk` | - | none |
| `lem-sfb-etale-proetale-scalar-counit-transposes` | - | none |
| `lem-sfb-exact-tensor-functor-derived-braiding` | - | none |
| `lem-sfb-exact-tensor-functor-derived-normalization` | - | none |
| `lem-sfb-finite-proper-classical-coproducts` | - | none |
| `lemma-nagata-affine-finite-type-is-quasi-affine` | - | none |
| `lemma-nagata-localization-ideal-pow` | - | none |
| `def-nagata-relative-stage-morphism-data` | - | none |
| `def-sc-zariski-flasque` | - | none |
| `lem-a1-mixed-direct-summand` | - | none |
| `lem-pur-adic-scalar-trace-coherence` | - | none |
| `lem-sfb-derived-direct-image-open-coherence` | - | none |
| `lem-sfb-joint-adjunction-model-embedding` | - | none |
| `lem-sfb-locally-prescribed-modules-small` | - | none |
| `lem-sfb-small-triangulated-extension-classes` | - | none |
| `lem-sfb-trace-base-change-first` | - | none |
| `lem-sfb-weak-serre-bounded-thick` | - | none |
| `lem-wf-tate-twist-frobenius` | - | none |
| `lemma-nagata-relative-stage-morphism-data-exists` | - | none |
| `def-trf-supported-class` | - | none |
| `def-wf-tate-twist` | - | none |
| `lem-a1-constructible-pullback-t-exact` | - | none |
| `lem-a1-extension-bounds` | - | none |
| `lem-fd-rational-coefficient-category-comparison` | - | none |
| `lem-per-continuous-rational-derived-realization` | - | none |
| `lem-sfb-local-model-cohomology-descent` | - | none |
| `lem-wf-tate-twist-compatibility` | - | none |
| `lem-zl-complex-extension` | - | none |
| `thm-zl-relative-line-stratification` | - | none |
| `def-mg-determinant-line` | - | none |
| `def-nagata-affine-neighbourhood-generic-points` | - | none |
| `def-nagata-strict-transform-closed-chart-model` | - | none |
| `lem-a1-punctual-bound-module-mixed` | - | none |
| `lem-per-adic-heart-pullback-fibres` | - | none |
| `lem-pur-reduction-limit-shift-adjunction` | - | none |
| `lem-sfb-coefficient-sections-localization` | - | none |
| `lem-wf-internal-hom-weil` | - | none |
| `lem-wf-tensor-weil` | - | none |
| `lemma-nagata-strict-transform-chart-localization-data` | - | none |
| `def-nagata-strict-transform-chart-comparison-localized` | - | none |
| `def-nagata-strict-transform-chart-ring` | - | none |
| `def-per-perverse-subcategories` | - | none |
| `def-per-support-condition` | - | none |
| `def-sc-general-curve` | - | none |
| `def-sfb-right-derived-exact` | - | none |
| `def-wf-constant-weil-twist` | - | none |
| `det-uniform-constructible-ext-integral` | - | none |
| `lem-dl-a1-weil-kernel-inertia` | - | none |
| `prop-wf-weil-sheaf-representation-equivalence` | - | none |
| `thm-nagata-blowup-flat-base-change` | - | none |
| `thm-zl-real-mixed-by-curves` | - | none |
| `def-nagata-blowup-flat-base-change-map` | - | none |
| `def-nagata-strict-transform-chart-comparison` | - | none |
| `def-wf-iota-real` | - | none |
| `det-lem-stratified-lattice-rank` | - | none |
| `lem-per-dual-lisse-tensor` | - | none |
| `lem-zl-curve-testing-irreducibility` | - | none |
| `lemma-nagata-flat-pullback-rees` | - | none |
| `def-nagata-flat-pullback-rees-map` | - | none |
| `def-nagata-strict-chart-to-extended-blowup-chart` | - | none |
| `lem-zl-bertini-finite-cover-curve` | - | none |
| `lemma-nagata-separate-closed-data-exists` | - | none |
| `sk-def-sf-categories` | - | none |
| `def-nagata-sheaf-rees-algebra` | - | none |
| `lem-fd-local-weil-model-trace-independence` | - | none |
| `sk-d-real-weights` | - | none |
| `def-fd-additive-character` | - | none |
| `lem-mg-common-positive-central-element` | - | none |
| `lem-mg-degree-component-functoriality` | - | none |
| `lemma-nagata-sheaf-ideal-powers-assoc` | - | none |
| `sk-d-real-operations` | - | none |
| `sk-d-real-weil` | - | none |
| `def-fd-kernel` | - | none |
| `sk-def-av` | - | none |
| `def-wf-lie-radical-centre` | - | none |
| `sk-def-kernel` | - | none |
| `sk-lem-as-properties` | - | none |
| `def-wf-semisimple-lie-algebra` | - | none |
| `sk-thm-picard-semicon` | - | none |
| `lem-pc-finite-linear-avoidance` | - | none |

## Stage 2: nodes to state (103)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-padic-condensed-ring` | 1 | state | 267 |
| `def-sfb-modobj-coextension` | 1 | state | 238 |
| `def-sfb-modobj-linearization` | 1 | state | 231 |
| `def-sfb-modobj-linearization-right-adjoint` | 2 | state | 230 |
| `def-sfb-modobj-transport-adjunction` | 1 | state | 229 |
| `def-sfb-integers-to-subfield-point` | 2 | state | 57 |
| `def-sfb-modobj-symmetric-tensor` | 2 | state | 20 |
| `sk-def-curve` | 2 | state | 10 |
| `sk-d-real-setup` | 1 | state | 4 |
| `sk-def-sfb-finite-derived-functors` | 1 | state | 3 |
| `def-sfb-bounded-constructible-complexes` | 1 | state | 2 |
| `def-sfb-extend-comap-iso-of-iso` | 1 | state | 0 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `def-sfb-extend-scalars-iso-of-eq` | 2 | state | 0 |
| `lem-sfb-modobj-symmetric-bimodules` | 1 | state | 244 |
| `lem-sfb-kflat-scalar-comparison-normalization` | 1 | state | 3 |
| `lem-weil-pbc-realization-scalar-functor` | 1 | state | 3 |
| `lem-fix-proetale-scalar-mate-normalization` | 1 | state | 1 |
| `lem-pd-section-derived-pushpull-normalization` | 1 | state | 1 |
| `lem-pd-section-ordinary-oplax-normalization` | 1 | state | 1 |
| `lem-pe-principal-reduction-cone-calculus` | 1 | state | 1 |
| `lem-pur-finite-free-completion-exchange` | 1 | state | 1 |
| `lem-weil-pbc-reduction-pullback-derived-tower` | 1 | state | 1 |
| `lem-cbc-constant-derived-limit-resolution-unit` | 1 | state | 0 |
| `lem-cbc-derived-constant-tower-normalization` | 1 | state | 0 |
| `lem-cbc-derived-tower-evaluation-normalization` | 1 | state | 0 |
| `lem-cbc-finite-constant-map-naturality` | 1 | state | 0 |
| `lem-cbc-open-localized-counit-comparison` | 1 | state | 0 |
| `lem-cbc-strict-quotient-pullback-computation` | 1 | state | 0 |
| `lem-fix-reduction-open-etale-origin` | 1 | state | 0 |
| `lem-pd-monoidal-adjunction-equivalence-transport` | 1 | state | 0 |
| `lem-pd-ringed-direct-image-pairing-lax` | 1 | state | 0 |
| `lem-pd-ringed-tensor-adjunction-mate` | 1 | state | 0 |
| `lem-pe-comparison-etale-slice-abelian-pullback` | 1 | state | 0 |
| `lem-pe-finite-coefficient-model-comparison` | 1 | state | 0 |
| `lem-pe-finite-scalar-restriction-constructible` | 1 | state | 0 |
| `lem-pe-integral-completion-presentation` | 1 | state | 0 |
| `lem-pe-ringed-site-derived-evaluation-slice` | 1 | state | 0 |
| `lem-pur-additive-localization-descent` | 1 | state | 0 |
| `lem-pur-adic-line-system-base-change` | 1 | state | 0 |
| `lem-pur-compatible-coefficient-tower` | 1 | state | 0 |
| `lem-pur-diagram-ring-restriction-pushforward` | 1 | state | 0 |
| `lem-pur-integral-ambient-operation-models` | 1 | state | 0 |
| `lem-pur-roos-intrinsic-completeness-equivalence` | 1 | state | 0 |
| `lem-pur-scalar-hom-comparison-tower` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-pur-strict-roos-homotopy-functor` | 1 | state | 0 |
| `lem-pur-torsion-line-system-base-change` | 1 | state | 0 |
| `lem-sbc-koszul-fibre-linear-descent` | 1 | state | 0 |
| `lem-sbc-reflected-compositor-unit-normalization` | 1 | state | 0 |
| `lem-sbc-reflector-adjunction-unit-formulas` | 1 | state | 0 |
| `lem-sbc-reflector-square-mate-factorization` | 1 | state | 0 |
| `lem-sbc-strict-quotient-exchange-unit-equation` | 1 | state | 0 |
| `lem-sbc-unbounded-exact-adjunction-square` | 1 | state | 0 |
| `lem-sf-bounded-below-hom-test` | 1 | state | 0 |
| `lem-sf-open-finite-constructibility-interval` | 1 | state | 0 |
| `lem-sf-ringed-open-roos-preservation` | 1 | state | 0 |
| `lem-sf-ringed-open-total-tensor-kflat` | 1 | state | 0 |
| `lem-sfb-adic-perfect-model-complete-reduction` | 1 | state | 0 |
| `lem-sfb-adic-stratum-completion-unit` | 1 | state | 0 |
| `lem-sfb-closed-support-bounded-continuity` | 1 | state | 0 |
| `lem-sfb-coefficient-projection-square` | 1 | state | 0 |
| `lem-sfb-coefficient-push-filtered-legs` | 1 | state | 0 |
| `lem-sfb-constant-field-tor-bounds` | 1 | state | 0 |
| `lem-sfb-constructible-local-tor-etale-origin` | 1 | state | 0 |
| `lem-sfb-derived-exchange-exact-normalization` | 1 | state | 0 |
| `lem-sfb-equivalence-square-inverse-mate-coherence` | 1 | state | 0 |
| `lem-sfb-eta-ring-hom` | 1 | state | 0 |
| `lem-sfb-finite-discrete-constructible-model` | 1 | state | 0 |
| `lem-sfb-finite-etale-trace-image` | 1 | state | 0 |
| `lem-sfb-finite-field-lisse-internal-hom` | 1 | state | 0 |
| `lem-sfb-finite-proper-classical-neighborhood-vanishing` | 1 | state | 0 |
| `lem-sfb-flat-dvr-scalar-tensor` | 1 | state | 0 |
| `lem-sfb-hom-kflat-chain-transpose` | 1 | state | 0 |
| `lem-sfb-integral-derived-extension-comparison` | 1 | state | 0 |
| `lem-sfb-internal-section-scalar-adjunction` | 1 | state | 0 |
| `lem-sfb-lattice-pullback` | 1 | state | 0 |
| `lem-sfb-lfp-scalar-isomorphism` | 1 | state | 0 |
| `lem-sfb-local-integral-perfect-model-cohomology` | 1 | state | 0 |
| `lem-sfb-modobj-kernels` | 1 | state | 0 |
| `lem-sfb-normalized-immersion-comparison-coherence` | 1 | state | 0 |
| `lem-sfb-open-module-restriction-identities` | 1 | state | 0 |
| `lem-sfb-projection-comparison-etale-proetale` | 1 | state | 0 |
| `lem-sfb-rational-derived-scalar-invertible` | 1 | state | 0 |
| `lem-sfb-ringed-complete-triangulated` | 1 | state | 0 |
| `lem-sfb-scalar-inverse-image-tower-diagram` | 1 | state | 0 |
| `lem-sfb-scalar-presentation-cokernel` | 1 | state | 0 |
| `lem-sfb-shriek-coefficient-isomorphism` | 1 | state | 0 |
| `lem-sfb-stratified-local-cohomological-bounds` | 1 | state | 0 |
| `lem-sfb-tor-interval-local-detection` | 1 | state | 0 |
| `lem-sp-etale-sum-coefficient-computation` | 1 | state | 0 |
| `lem-sp-open-scalar-site-coherence` | 1 | state | 0 |
| `lem-sp-smooth-admissible-coordinate-cover` | 1 | state | 0 |
| `lem-weil-pbc-bounded-complex-triangulated-devissage` | 1 | state | 0 |
| `lem-weil-pbc-coherent-affine-base-change-edge-naturality` | 1 | state | 0 |
| `lem-weil-pbc-finite-basis-cech-first-limit` | 1 | state | 0 |
| `lem-weil-pbc-finite-etale-cover-cech-stage-comparison` | 1 | state | 0 |
| `lem-weil-pbc-flat-scalar-restriction-kflat` | 1 | state | 0 |
| `lem-weil-pbc-strict-perfect-ringed-pullback-model` | 1 | state | 0 |
| `sk-lem-sf-determination` | 1 | state | 0 |
| `lem-cbc-derived-finite-quotient-coherence` | 2 | state | 0 |
| `lem-sfb-finite-classical-localizing` | 2 | state | 0 |
| `lem-sfb-subfield-push-iso` | 2 | state | 0 |

Not open yet: 369 nodes that below a finished node, not needed, 25 nodes that wait for stage 1 deeper in its statement downstream, 95 nodes that wait for stage 1 (statement downstream not grounded), 124 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (175)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | - | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | route |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | 4 | 1 | proof | route |
| `Sheaf.Paper.AdicCoefficientDatumCompleted` | 6 | 6 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.SfDerivedDirectImage` | 4 | 4 | proof | 1 |
| `Sheaf.Algebra.Homology.InternalHomLocalizationComparison` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.LeftModuleComparisonVanishingCriterion` | - | 1 | proof | 1 |
| `Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 13 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | - | 21 | proof | 1 |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.LocalFrobeniusTrace` | - | 5 | proof | 1 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 1 |
| `Sheaf.Paper.PointFibreEquivalence` | - | 1 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | - | 3 | proof | 1 |
| `Sheaf.Paper.SquareZeroPeriodicTensor` | - | 2 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 2 | proof | 2 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.RHomContinuityTriangleClosure` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.CategoryTheory.FormalExactProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarCoordinateLimitCriterion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.NumberTheory.Padics.FiniteSumLattice` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CommonStageCalculus` | - | 8 | proof | 2 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | proof | 2 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 2 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | - | 27 | proof | 2 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | - | 4 | proof | 2 |
| `Sheaf.Paper.ConstructibleTruncations` | - | 1 | proof | 2 |
| `Sheaf.Paper.ContinuousLatticeSum` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayama` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | - | 7 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCtfTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 9 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | proof | 2 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 13 | proof | 2 |
| `Sheaf.Paper.WeilIndSheafCategory` | - | 8 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | - | 2 | proof | 2 |
| `Sheaf.TraceFormula.PointTransportComposition` | - | 2 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatScalarCyclicResolution` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DirectImageRoosNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | - | 7 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 3 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | - | 19 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | - | 3 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 3 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.FiniteSubextensionsDirected` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | - | 7 | proof | 3 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | - | 1 | proof | 3 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | proof | 3 |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | - | 1 | proof | 3 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 3 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientPullbackComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 7 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 7 | proof | 3 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 13 | 3 | proof | 4 |
| `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.RoosConeCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteCompactSiteCoherence` | - | 11 | proof | 4 |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSlicePullbackMateNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | proof | 4 |
| `Sheaf.RingTheory.ModuleLocalizationFilteredColimit` | 10 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` | - | 1 | proof | 5 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | - | 1 | proof | 8 |

## Stage 3: waiting for statements of dependencies (44)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-finite-discrete-constructible-model` |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 2 | `lem-sfb-qlbar-point-abelian-colimit` |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | 3 | 1 | `lem-sf-etale-origin-pushforward-amplitude` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | 4 | 2 | `def-sfb-integers-to-subfield-point` |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | `lem-sfb-hom-kflat-chain-transpose` |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | - | 1 | `lem-sfb-constructible-local-tor-etale-origin` |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | - | 1 | `lem-sfb-scalar-presentation-cokernel` |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | `lem-weil-pbc-flat-curve-derived-structure-model` |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | `lem-cbc-finite-constant-map-naturality` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-adic-line-system-base-change` |
| `Sheaf.Paper.CartesianCoefficients` | - | 2 | `def-sfb-modobj-extension-along-iso` |
| `Sheaf.Paper.CompactSupportReductionTower` | - | 1 | `lem-pur-sequence-site-completion-projection` |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | `lem-pur-diagram-ring-restriction-pushforward` |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | `lem-cbc-ringed-open-flat-resolution` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-flat-coefficient-reduction-adjunct` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | `lem-pe-completion-triangle-comparison` |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | `lem-sp-proetale-scalar-tensor-normalization` |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | - | 3 | `lem-fix-reduction-open-etale-origin` |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | `lem-sfb-projection-comparison-etale-proetale` |
| `Sheaf.Paper.FlatCommonQuotientReductionTower` | - | 1 | `lem-weil-pbc-flat-scalar-restriction-kflat` |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | - | 1 | `lem-sfb-local-integral-perfect-model-cohomology` |
| `Sheaf.Paper.IntegralCriterionReductions` | - | 8 | `lem-pe-finite-coefficient-model-comparison` |
| `Sheaf.Paper.IntegralModels` | - | 1 | `lem-sfb-constant-field-tor-bounds` |
| `Sheaf.Paper.IntegralModelsOperations` | - | 1 | `lem-sfb-scalar-model-immersion-extension` |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | `lem-pur-finite-free-completion-exchange` |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | - | 1 | `lem-weil-pbc-integral-constructible-hom-sums` |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | - | 1 | `lem-sfb-tor-interval-local-detection` |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | `lem-pd-section-derived-pushpull-normalization` |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | - | 3 | `lem-pd-ringed-direct-image-pairing-lax` |
| `Sheaf.Paper.PurityConventions` | - | 11 | `sk-def-sf-operations` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | `lem-sbc-koszul-fibre-linear-descent` |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | - | 2 | `lem-sf-ringed-open-total-tensor-kflat` |
| `Sheaf.Paper.StratifiedLattice` | - | 1 | `lem-sfb-lattice-pullback` |
| `Sheaf.Paper.TateTwistLocallyFree` | - | 1 | `lem-pur-line-unbounded-derived-tensor` |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | - | 1 | `lem-sf-open-extension-scalar-restriction-coherence` |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | `lem-sp-restricted-scalar-cohomology-local-constancy` |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | - | 1 | `lem-sfb-weak-serre-bounded-thick` |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | `lem-sfb-finite-proper-classical-neighborhood-vanishing` |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | - | 1 | `def-sfb-modobj-symmetric-tensor` |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | `lem-sfb-lattice-subquotient-filtration` |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | `lem-sfb-closed-supported-scalar-comparison` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `def-sfb-extend-scalars-iso-of-eq` |

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
