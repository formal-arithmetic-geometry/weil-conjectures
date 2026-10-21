# Work queue

418 items; claim with `tools/claim.py next <group> [--stage N]`.

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

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 72, stage 3 169 items.

## Stage 1: nodes to split (160)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-qbar-condensed-two-colimit` | 0 | none |
| `prop-weil-pbc-scalar-extension` | 1 | none |
| `lem-pur-finite-coefficient-adjoint-comparisons` | 3 | none |
| `lem-weil-pbc-flat-coefficient-reduction-adjunct` | 5 | none |
| `lem-weil-pbc-flat-scalar-koszul-tower-comparison` | 5 | none |
| `lem-weil-pbc-pulled-reduction-normalization-comparison` | 5 | none |
| `lem-weil-pbc-pulled-reduction-strict-tower-comparison` | 5 | none |
| `sk-thm-purity-transport` | 5 | none |
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
| `lem-pur-adic-basis-limit` | 1003 | none |
| `lem-pur-finite-free-quotient-completion` | 1003 | none |
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
| `lem-sf-open-finite-constructibility-interval` | 1003 | none |
| `lem-sf-fixed-pair-adjunction-lift` | 1017 | none |
| `lem-pur-completed-line-tensor-coherence` | 2001 | none |
| `lem-pur-integral-line-reduction-restriction` | 2001 | none |
| `lem-pur-line-unbounded-derived-tensor` | 2001 | none |
| `det-sf-comp-coherence-cocycle` | 2003 | none |
| `lem-sf-etale-origin-pushforward-amplitude` | 2003 | none |
| `lem-sf-finite-proetale-pushforward-constructible` | 2003 | none |
| `lem-sf-nilpotent-coefficient-direct-image-bound` | 2003 | none |
| `lem-cbc-completed-ring-strict-finite-exchange` | 2004 | none |
| `lem-cbc-exact-linear-koszul-fiber` | 2004 | none |
| `lem-cbc-ringed-open-flat-resolution` | 2004 | none |
| `lem-cbc-ringed-open-strict-reduction` | 2004 | none |
| `lem-pur-etale-compact-scalar-coherence` | 2005 | none |
| `sk-def-sf-admissible` | 2005 | none |
| `lem-sfb-coherent-right-adjoint-comparisons` | 2006 | none |
| `lem-fix-operation-reduction` | 3002 | none |
| `lemma-nagata-open-immersion-qc-over-separated-target` | 3003 | none |
| `def-kun-separably-closed` | 3004 | none |
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
| `sk-thm-picard-rr` | 3014 | none |
| `sk-thm-picard-duality` | 3015 | none |
| `prop-nagata-proj-standard-open` | 3023 | none |
| `def-pod-perfect-derived-pairing` | 4007 | none |
| `lem-coef-closed-adjunction-enriched-isomorphism` | 5003 | none |
| `lem-coef-enriched-sequence-projection-formula` | 5003 | none |
| `lem-coef-ringed-pullback-hom-evaluation-comparison` | 5003 | none |
| `lem-coef-sequence-global-sections-evaluation` | 5003 | none |
| `lem-coef-sequence-projection-derived-adjunction` | 5003 | none |
| `lem-coef-sequence-pushforward-limit-projections` | 5003 | none |
| `lem-coef-sequence-sections-limit-comparison` | 5003 | none |
| `sk-def-sf-kv-maps` | 5005 | none |
| `lem-trf-weakly-etale-between-objects` | 5007 | none |
| `sk-lem-picard-cech-computes` | 5017 | none |
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
| `lem-sfb-localized-basis-coefficients` | - | none |
| `sk-def-cohfamily` | - | none |
| `sk-lem-integral-models` | - | none |
| `sk-prop-sfb-cartesian-coefficients` | - | none |
| `def-sfb-left-derived-functor` | - | none |
| `lem-pe-kflat-scalar-tower-realization` | - | none |
| `lem-pe-two-term-reduction-cohomology` | - | none |
| `lem-sp-etale-ctf-chart-domain` | - | none |
| `lem-sp-restricted-scalar-cohomology-local-constancy` | - | none |
| `lem-sp-signed-tate-coefficient-exponent-normalization` | - | none |
| `def-nagata-final-basechanged-compactification` | - | none |
| `def-nagata-final-fp-envelope` | - | none |
| `def-nagata-scheme-image-comparison` | - | none |
| `def-weil-complex-weights` | - | none |
| `def-weil-punctual-weights` | - | none |
| `lem-sfb-module-object-ringed-site-derived-comparison` | - | none |
| `lemma-nagata-final-noetherian-compactification` | - | none |
| `sk-def-perfect` | - | none |
| `def-nagata-extended-ideal` | - | none |
| `def-nagata-final-noetherian-compactification` | - | none |
| `def-nagata-immersion-into-fp-model` | - | none |
| `def-nagata-immersion-shrink-to-closed` | - | none |
| `def-nagata-rees-algebra` | - | none |
| `def-trf-trace-class-source` | - | none |
| `i-relative-frob` | - | none |
| `lemma-nagata-affine-finite-type-is-quasi-affine` | - | none |
| `lemma-nagata-localization-ideal-pow` | - | none |
| `def-nagata-relative-stage-morphism-data` | - | none |
| `def-sc-zariski-flasque` | - | none |
| `lem-a1-mixed-direct-summand` | - | none |
| `lem-sfb-joint-adjunction-model-embedding` | - | none |
| `lem-sfb-locally-prescribed-modules-small` | - | none |
| `lem-sfb-small-triangulated-extension-classes` | - | none |
| `lem-sfb-weak-serre-bounded-thick` | - | none |
| `lem-wf-tate-twist-frobenius` | - | none |
| `lemma-nagata-relative-stage-morphism-data-exists` | - | none |
| `def-trf-supported-class` | - | none |
| `lem-wf-tate-twist-compatibility` | - | none |
| `lem-zl-complex-extension` | - | none |
| `def-mg-determinant-line` | - | none |
| `def-nagata-affine-neighbourhood-generic-points` | - | none |
| `def-nagata-strict-transform-closed-chart-model` | - | none |
| `lem-wf-internal-hom-weil` | - | none |
| `lem-wf-tensor-weil` | - | none |
| `lemma-nagata-strict-transform-chart-localization-data` | - | none |
| `def-nagata-strict-transform-chart-comparison-localized` | - | none |
| `def-nagata-strict-transform-chart-ring` | - | none |
| `def-sc-general-curve` | - | none |
| `def-sfb-right-derived-exact` | - | none |
| `thm-nagata-blowup-flat-base-change` | - | none |
| `def-nagata-blowup-flat-base-change-map` | - | none |
| `def-nagata-strict-transform-chart-comparison` | - | none |
| `def-wf-iota-real` | - | none |
| `lemma-nagata-flat-pullback-rees` | - | none |
| `def-nagata-flat-pullback-rees-map` | - | none |
| `def-nagata-strict-chart-to-extended-blowup-chart` | - | none |
| `lemma-nagata-separate-closed-data-exists` | - | none |
| `sk-def-sf-categories` | - | none |
| `def-nagata-sheaf-rees-algebra` | - | none |
| `prop-wf-weil-sheaf-representation-equivalence` | - | none |
| `sk-d-real-weights` | - | none |
| `def-fd-additive-character` | - | none |
| `lem-mg-common-positive-central-element` | - | none |
| `lem-mg-degree-component-functoriality` | - | none |
| `lemma-nagata-sheaf-ideal-powers-assoc` | - | none |
| `sk-d-real-operations` | - | none |
| `sk-d-real-weil` | - | none |
| `lem-per-dual-lisse-tensor` | - | none |
| `sk-def-av` | - | none |
| `def-per-perverse-subcategories` | - | none |
| `def-per-support-condition` | - | none |
| `def-wf-lie-radical-centre` | - | none |
| `sk-def-kernel` | - | none |
| `sk-lem-as-properties` | - | none |
| `def-wf-semisimple-lie-algebra` | - | none |
| `sk-thm-picard-semicon` | - | none |
| `lem-pc-finite-linear-avoidance` | - | none |

## Stage 2: nodes to state (116)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-padic-condensed-ring` | 1 | state | 266 |
| `def-sfb-modobj-coextension` | 1 | state | 236 |
| `def-sfb-modobj-linearization` | 1 | state | 226 |
| `def-sfb-modobj-linearization-right-adjoint` | 2 | state | 225 |
| `def-sfb-modobj-transport-adjunction` | 1 | state | 224 |
| `def-sfb-integers-to-subfield-point` | 2 | state | 57 |
| `def-sfb-modobj-symmetric-tensor` | 2 | state | 20 |
| `sk-def-curve` | 2 | state | 10 |
| `sk-d-real-setup` | 1 | state | 4 |
| `sk-def-sfb-finite-derived-functors` | 1 | state | 3 |
| `def-sfb-bounded-constructible-complexes` | 1 | state | 2 |
| `def-wf-internal-hom` | 2 | state | 2 |
| `def-sfb-extend-comap-iso-of-iso` | 1 | state | 0 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `def-sfb-extend-scalars-iso-of-eq` | 2 | state | 0 |
| `lem-sfb-modobj-symmetric-bimodules` | 1 | state | 242 |
| `lem-sfb-kflat-scalar-comparison-normalization` | 1 | state | 3 |
| `lem-weil-pbc-realization-scalar-functor` | 1 | state | 3 |
| `lem-fix-proetale-scalar-mate-normalization` | 1 | state | 1 |
| `lem-pur-finite-free-completion-exchange` | 1 | state | 1 |
| `lem-sf-semilinear-scalar-ordinary-comparison` | 1 | state | 1 |
| `lem-sfb-exact-open-closed-unbounded-calculus` | 1 | state | 1 |
| `lem-sp-etale-derived-chain-transpose` | 1 | state | 1 |
| `lem-weil-pbc-constant-tower-pushforward-normalization` | 1 | state | 1 |
| `lem-weil-pbc-reduction-pullback-derived-tower` | 1 | state | 1 |
| `lem-cbc-derived-constant-tower-normalization` | 1 | state | 0 |
| `lem-cbc-derived-tower-evaluation-normalization` | 1 | state | 0 |
| `lem-cbc-finite-constant-map-naturality` | 1 | state | 0 |
| `lem-cbc-open-localized-counit-comparison` | 1 | state | 0 |
| `lem-fix-reduction-open-etale-origin` | 1 | state | 0 |
| `lem-pd-monoidal-adjunction-equivalence-transport` | 1 | state | 0 |
| `lem-pd-ringed-direct-image-pairing-lax` | 1 | state | 0 |
| `lem-pd-ringed-tensor-adjunction-mate` | 1 | state | 0 |
| `lem-pe-comparison-etale-slice-abelian-pullback` | 1 | state | 0 |
| `lem-pe-finite-scalar-restriction-constructible` | 1 | state | 0 |
| `lem-pe-ringed-site-derived-evaluation-slice` | 1 | state | 0 |
| `lem-pur-additive-localization-descent` | 1 | state | 0 |
| `lem-pur-adic-line-system-base-change` | 1 | state | 0 |
| `lem-pur-compatible-coefficient-tower` | 1 | state | 0 |
| `lem-pur-diagram-ring-restriction-pushforward` | 1 | state | 0 |
| `lem-pur-integral-ambient-operation-models` | 1 | state | 0 |
| `lem-pur-scalar-hom-comparison-tower` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-pur-site-representable-algebraic-pullback` | 1 | state | 0 |
| `lem-pur-strict-roos-homotopy-functor` | 1 | state | 0 |
| `lem-pur-torsion-line-system-base-change` | 1 | state | 0 |
| `lem-sbc-koszul-fibre-linear-descent` | 1 | state | 0 |
| `lem-sbc-reflected-compositor-unit-normalization` | 1 | state | 0 |
| `lem-sbc-reflector-adjunction-unit-formulas` | 1 | state | 0 |
| `lem-sbc-reflector-square-mate-factorization` | 1 | state | 0 |
| `lem-sbc-strict-quotient-exchange-unit-equation` | 1 | state | 0 |
| `lem-sbc-unbounded-exact-adjunction-square` | 1 | state | 0 |
| `lem-sf-adjunct-conjugate-open-factor` | 1 | state | 0 |
| `lem-sf-bounded-below-hom-test` | 1 | state | 0 |
| `lem-sf-ringed-open-roos-preservation` | 1 | state | 0 |
| `lem-sf-ringed-open-total-tensor-kflat` | 1 | state | 0 |
| `lem-sf-semilinear-alpha-pullback` | 1 | state | 0 |
| `lem-sf-semilinear-clopen-unit-projector` | 1 | state | 0 |
| `lem-sf-semilinear-compositor-coherence` | 1 | state | 0 |
| `lem-sfb-adic-perfect-model-complete-reduction` | 1 | state | 0 |
| `lem-sfb-adic-stratum-completion-unit` | 1 | state | 0 |
| `lem-sfb-closed-support-bounded-continuity` | 1 | state | 0 |
| `lem-sfb-constant-scalar-geometric-adjunctions` | 1 | state | 0 |
| `lem-sfb-constant-scalar-restriction-tensor` | 1 | state | 0 |
| `lem-sfb-derived-exchange-exact-normalization` | 1 | state | 0 |
| `lem-sfb-equivalence-square-inverse-mate-coherence` | 1 | state | 0 |
| `lem-sfb-filtered-colimit-flat-module-sheaves` | 1 | state | 0 |
| `lem-sfb-finite-etale-trace-image` | 1 | state | 0 |
| `lem-sfb-finite-proper-classical-neighborhood-vanishing` | 1 | state | 0 |
| `lem-sfb-flat-dvr-scalar-tensor` | 1 | state | 0 |
| `lem-sfb-hom-kflat-chain-transpose` | 1 | state | 0 |
| `lem-sfb-integral-derived-extension-comparison` | 1 | state | 0 |
| `lem-sfb-internal-scalar-extension-section-test` | 1 | state | 0 |
| `lem-sfb-internal-section-scalar-adjunction` | 1 | state | 0 |
| `lem-sfb-lattice-pullback` | 1 | state | 0 |
| `lem-sfb-lfp-scalar-isomorphism` | 1 | state | 0 |
| `lem-sfb-local-integral-perfect-model-cohomology` | 1 | state | 0 |
| `lem-sfb-normalized-immersion-comparison-coherence` | 1 | state | 0 |
| `lem-sfb-projection-comparison-etale-proetale` | 1 | state | 0 |
| `lem-sfb-rational-derived-scalar-invertible` | 1 | state | 0 |
| `lem-sfb-ring-isomorphism-tensor-transport` | 1 | state | 0 |
| `lem-sfb-ringed-complete-triangulated` | 1 | state | 0 |
| `lem-sfb-scalar-coordinate-limit-criterion` | 1 | state | 0 |
| `lem-sfb-scalar-inverse-image-tower-diagram` | 1 | state | 0 |
| `lem-sfb-scalar-normalized-constant-models` | 1 | state | 0 |
| `lem-sfb-scalar-presentation-cokernel` | 1 | state | 0 |
| `lem-sfb-shriek-coefficient-isomorphism` | 1 | state | 0 |
| `lem-sfb-stratified-local-cohomological-bounds` | 1 | state | 0 |
| `lem-sfb-tor-interval-local-detection` | 1 | state | 0 |
| `lem-sp-etale-sum-coefficient-computation` | 1 | state | 0 |
| `lem-sp-exact-derived-transformation-pasting` | 1 | state | 0 |
| `lem-sp-finite-compact-site-coherence` | 1 | state | 0 |
| `lem-sp-open-scalar-site-coherence` | 1 | state | 0 |
| `lem-sp-ordinary-horizontal-pasting-transport` | 1 | state | 0 |
| `lem-sp-ordinary-vertical-pasting-transport` | 1 | state | 0 |
| `lem-sp-smooth-admissible-coordinate-cover` | 1 | state | 0 |
| `lem-sp-varying-ring-cartesian-comparison-lift-relabelling` | 1 | state | 0 |
| `lem-sp-varying-ring-cartesian-lift-pullback-equivalence` | 1 | state | 0 |
| `lem-sp-varying-ring-open-unit-coherence` | 1 | state | 0 |
| `lem-sp-varying-ring-pullback-unit-coherence` | 1 | state | 0 |
| `lem-weil-pbc-bounded-complex-triangulated-devissage` | 1 | state | 0 |
| `lem-weil-pbc-coherent-affine-base-change-edge-naturality` | 1 | state | 0 |
| `lem-weil-pbc-discrete-exchange-site-comparison` | 1 | state | 0 |
| `lem-weil-pbc-finite-basis-cech-first-limit` | 1 | state | 0 |
| `lem-weil-pbc-finite-etale-cover-cech-stage-comparison` | 1 | state | 0 |
| `lem-weil-pbc-flat-constant-tensor-pro-zero-cones` | 1 | state | 0 |
| `lem-weil-pbc-flat-scalar-restriction-kflat` | 1 | state | 0 |
| `lem-weil-pbc-heart-test-bounded-below` | 1 | state | 0 |
| `lem-weil-pbc-pullback-tensor-canonical-shift-unit` | 1 | state | 0 |
| `lem-weil-pbc-ringed-common-quotient-pullback-comparison` | 1 | state | 0 |
| `lem-weil-pbc-stratum-completion-unit-restriction` | 1 | state | 0 |
| `lem-weil-pbc-strict-perfect-ringed-pullback-model` | 1 | state | 0 |
| `sk-lem-sf-determination` | 1 | state | 0 |
| `lem-sfb-base-coefficient-condensed-identification` | 2 | state | 0 |
| `lem-sfb-finite-classical-localizing` | 2 | state | 0 |
| `lem-sfb-modobj-cokernels` | 3 | state | 0 |

Not open yet: 371 nodes that below a finished node, not needed, 79 nodes that wait for stage 1 (statement downstream not grounded), 127 nodes that wait for a statement dependency (bottom-up), 6 nodes that wait for stage 1 deeper in its statement downstream.

## Stage 3: modules to prove (121)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 11 | 1 | repair | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | - | 4 | proof | route |
| `Sheaf.Algebra.Homology.InternalHomLocalizationComparison` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.LeftModuleComparisonVanishingCriterion` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.CohomologyTorInterval` | - | 1 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | - | 2 | proof | 1 |
| `Sheaf.Paper.ProEtaleConstructibleExactClosure` | - | 1 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | - | 1 | proof | 1 |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | - | 3 | proof | 1 |
| `Sheaf.Paper.SquareZeroPeriodicTensor` | - | 2 | proof | 1 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.RHomContinuityTriangleClosure` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.EtaleStalkTorTest` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.FormalExactProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.GrothendieckSheafification` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.LocalizingHomTest` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.MonoidalFiniteFreeTransport` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.FieldTheory.CondensedSubfieldBasis` | - | 1 | proof | 2 |
| `Sheaf.NumberTheory.Padics.FiniteSumLattice` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CompletedDirectImageLimits` | - | 2 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | - | 15 | proof | 2 |
| `Sheaf.Paper.ContinuousLatticeSum` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | - | 3 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 7 | proof | 2 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 4 | proof | 2 |
| `Sheaf.CategoryTheory.SheafificationTensorLocalIso` | 10 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatScalarCyclicResolution` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleAmbientOperationsScalarLinearity` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | - | 9 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProperGeometricFibreCohomologicalBound` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.Sites.ProperGeometricFibreTorsionBound` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedBifunctorDevissage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DirectImageRoosNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactDerivedComposition` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FilteredTwoColimitCharacterization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.FilteredTwoColimitModel` | - | 15 | proof | 3 |
| `Sheaf.CategoryTheory.RationalizationLocalizationHomCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | - | 4 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarUnitEqualityDetection` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.DerivedNakayamaResolution` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 3 | proof | 3 |
| `Sheaf.Paper.FiniteFieldStratifiedPerfectModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteSubextensionsDirected` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | - | 2 | proof | 3 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | - | 6 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientPullbackComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedSlicePullbackMateNormalization` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 9 | proof | 3 |
| `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.RoosConeCalculus` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.ScalarConeTensorModel` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.AffineRootsRepresentability` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | - | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactFaithfulTorsion` | - | 5 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | - | 3 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 2 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Topology.ProfiniteSectionsFiniteQuotient` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FinitePostnikovIsomorphism` | - | 1 | proof | 5 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarCounitTransposes` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` | - | 1 | proof | 5 |
| `Sheaf.RingTheory.ModuleLocalizationFilteredColimit` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.Paper.DivisibleExtensionDerivedReduction` | - | 5 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |

## Stage 3: waiting for statements of dependencies (41)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | `lem-sfb-hom-kflat-chain-transpose` |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | - | 1 | `lem-sfb-scalar-presentation-cokernel` |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | `lem-weil-pbc-flat-curve-derived-structure-model` |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | `lem-cbc-finite-constant-map-naturality` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-adic-line-system-base-change` |
| `Sheaf.Paper.CartesianCoefficients` | - | 2 | `def-sfb-modobj-extension-along-iso` |
| `Sheaf.Paper.CompactSupportReductionTower` | - | 1 | `lem-pur-sequence-site-completion-projection` |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | `lem-pur-diagram-ring-restriction-pushforward` |
| `Sheaf.Paper.CompletedCondensedCoefficients` | - | 2 | `lem-sfb-qlbar-point-abelian-colimit` |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | `lem-cbc-ringed-open-flat-resolution` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-flat-coefficient-reduction-adjunct` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | `lem-pe-completion-triangle-comparison` |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | `lem-sp-proetale-scalar-tensor-normalization` |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | - | 3 | `lem-fix-reduction-open-etale-origin` |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | `lem-sfb-projection-comparison-etale-proetale` |
| `Sheaf.Paper.FlatCommonQuotientReductionTower` | - | 1 | `lem-weil-pbc-flat-scalar-restriction-kflat` |
| `Sheaf.Paper.IntegralCriterionReductions` | - | 8 | `lem-pe-finite-coefficient-model-comparison` |
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
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | - | 1 | `lem-sf-etale-origin-pushforward-amplitude` |
| `Sheaf.Paper.SmoothPurityQbar` | - | 1 | `det-sp-integral-adjunction-bijection` |
| `Sheaf.Paper.StratifiedLattice` | - | 1 | `lem-sfb-lattice-pullback` |
| `Sheaf.Paper.TateTwistLocallyFree` | - | 1 | `lem-pur-line-unbounded-derived-tensor` |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | - | 1 | `lem-sf-open-extension-scalar-restriction-coherence` |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | `lem-sp-restricted-scalar-cohomology-local-constancy` |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | - | 1 | `lem-sfb-weak-serre-bounded-thick` |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | `lem-sfb-finite-proper-classical-neighborhood-vanishing` |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | `lem-sfb-lattice-subquotient-filtration` |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | `lem-sfb-closed-supported-scalar-comparison` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | - | 2 | `def-sfb-integers-to-subfield-point` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `def-sfb-extend-scalars-iso-of-eq` |
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
