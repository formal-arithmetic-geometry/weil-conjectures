# Work queue

722 items; claim with `tools/claim.py next <group> [--stage N]`.

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

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 127, stage 3 65 items.

## Stage 1: nodes to split (51)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-pd-section-derived-open-adjunction-normalization` | 2 | none |
| `lem-weil-pbc-adjunction-square-shift-mate` | 6 | none |
| `lem-weil-pbc-derived-square-shift-on-kinjectives` | 6 | none |
| `lem-weil-pbc-slice-tensor-integer-shift-compatibility` | 6 | none |
| `lem-weil-pbc-proetale-closed-underived-projection` | 11 | none |
| `lem-pur-normalized-scalar-comparison-realization` | 1005 | none |
| `lem-sfb-qcqs-proper-constructible-closed-base-change` | 2005 | none |
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-zl-condensed-stalk-frobenius-orbit-trace` | 2007 | none |
| `lem-pur-line-zero-class-exchange` | 2021 | none |
| `lem-pc-tate-residue-field-extension` | 3016 | none |
| `lem-pc-finite-potent-trace-calculus` | 3017 | none |
| `lem-pc-tate-abstract-residue-calculus` | 3017 | none |
| `lem-pc-tate-endomorphism-ideals` | 3017 | none |
| `lem-pc-tate-residue-lattice-identity` | 3017 | none |
| `lem-sf-package-base-change-domain-realization` | 4006 | none |
| `lem-sf-package-compactified-tower-comparisons` | 4006 | none |
| `lem-sf-package-localization-projection-realization` | 4006 | none |
| `lem-sf-package-normalized-orientation-perfect-duality` | 4006 | none |
| `lem-sfb-continuous-algcl-open-scalar-comparison` | 4008 | none |
| `lem-sfb-continuous-algcl-stratified-finite-models` | 4008 | none |
| `lem-sf-perfect-scalar-tensor-coherence` | 5005 | none |
| `lem-sf-derived-immersion-comparison-normalization` | 5006 | none |
| `lem-sf-locally-closed-closure-adjoint-realization` | 5006 | none |
| `lem-sf-locally-closed-closure-comparison-square` | 5006 | none |
| `lem-sf-locally-closed-relative-transpose-normalization` | 5006 | none |
| `lem-weil-isomorphism-scalar-tensor-kflat-model` | 5006 | none |
| `lem-weil-isomorphism-scalar-augmentation-cone` | 5007 | none |
| `lem-sf-boundary-bounded-tensor-comparison` | 5008 | none |
| `lem-sf-fully-faithful-exceptional-hom-transport` | 5008 | none |
| `lem-weil-ramified-pullback-tower-identification` | 5008 | none |
| `lem-weil-scalar-pullback-strict-cone-naturality` | 5008 | none |
| `lem-sf-completed-pullback-mate-factorization` | 6006 | none |
| `lem-sf-exact-pullback-counit-normalization` | 6006 | none |
| `lem-sfb-cohomology-tor-interval` | - | none |
| `lem-sfb-derived-scalar-localization-reflection` | - | none |
| `lem-sfb-kinjective-hom-scalar-telescope` | - | none |
| `lem-zl-constant-sheaf-weight-zero` | - | none |
| `sk-def-perfect` | - | none |
| `det-sp-composition-factors` | - | none |
| `lem-pod-pullback-identities-scalar-extension` | - | none |
| `det-sp-composition-comparisons` | - | none |
| `lem-sfb-intrinsic-finite-derived-pullback` | - | none |
| `lem-sfb-ordinary-proetale-direct-image-plus-comparison` | - | none |
| `lem-wf-tate-twist-frobenius` | - | none |
| `def-per-support-condition` | - | none |
| `lem-dl-a1-henselian-global-inertia-comparison` | - | none |
| `lem-dl-a1-normal-scheme-galois-inertia-presentation` | - | none |
| `lem-zl-reduced-frontier-mixed-gluing` | - | none |
| `lem-zl-two-point-curve-constituent-purity` | - | none |
| `lem-sfb-continuous-coefficient-free-rank` | - | none |

## Stage 2: nodes to state (249)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `sk-def-sf-admissible` | 1 | state | 25 |
| `sk-d-real-weil` | 1 | state | 2 |
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-per-rational-module-realization-functor` | 1 | state | 6 |
| `lem-pc-tate-dvr-residue-calculus` | 1 | state | 4 |
| `lem-pur-completed-primitive-counit-comparison` | 2 | state | 4 |
| `lem-pc-vector-bundle-principal-parts` | 1 | state | 3 |
| `lem-weil-pbc-constant-tower-pushforward-normalization` | 1 | state | 3 |
| `lem-pd-section-derived-pushpull-normalization` | 1 | state | 2 |
| `lem-per-adic-common-stage-truncations` | 1 | state | 2 |
| `lem-sfb-scalar-adjunction-unit-coefficient-normalization` | 1 | state | 2 |
| `lem-weil-pbc-strict-quotient-scalar-balancing` | 1 | state | 2 |
| `lem-weil-point-finite-free-sections-tensor` | 1 | state | 2 |
| `det-nagata-density-normalization-sheaves` | 1 | state | 1 |
| `lem-cbc-completed-ring-strict-finite-exchange` | 1 | state | 1 |
| `lem-coef-sequence-sections-limit-comparison` | 1 | state | 1 |
| `lem-pur-clopen-ringed-module-gluing` | 1 | state | 1 |
| `lem-pur-sequence-site-completion-projection` | 1 | state | 1 |
| `lem-pur-signed-line-scalar-tensor-tower` | 1 | state | 1 |
| `lem-pur-strict-quotient-diagonal-normalization` | 1 | state | 1 |
| `lem-sf-ringed-kflat-single-tensor-comparison` | 1 | state | 1 |
| `lem-sfb-scalar-hom-chain-evaluation` | 1 | state | 1 |
| `lem-sfb-slice-scalar-hom-chain-adjunction` | 1 | state | 1 |
| `lem-sp-ell-coefficient-fiber` | 1 | state | 1 |
| `lem-weil-constant-scalar-strict-unit` | 1 | state | 1 |
| `lem-weil-pbc-flat-scalar-tower-limit-square` | 1 | state | 1 |
| `lem-weil-pbc-integral-coefficient-presentation-comparison` | 1 | state | 1 |
| `lem-weil-pbc-pullback-tensor-canonical-shift-unit` | 1 | state | 1 |
| `lem-weil-pbc-pulled-reduction-strict-tower-comparison` | 1 | state | 1 |
| `lem-weil-pbc-realization-completed-pull` | 1 | state | 1 |
| `lem-weil-point-automorphism-restriction-natural` | 1 | state | 1 |
| `lem-a1-completed-perfect-scalar-pullback` | 1 | state | 0 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-a1-integral-stratum-chart-restrictions` | 1 | state | 0 |
| `lem-a1-normalized-roos-shift-comparison` | 1 | state | 0 |
| `lem-a1-point-realization-standard-cohomology` | 1 | state | 0 |
| `lem-a1-principal-koszul-strict-replacement` | 1 | state | 0 |
| `lem-a1-roos-intrinsic-unit-comparison` | 1 | state | 0 |
| `lem-a1-texact-coefficient-stage-descent` | 1 | state | 0 |
| `lem-amb-finite-root-site-comparison` | 1 | state | 0 |
| `lem-cbc-flat-scalar-direct-image-limit-coherence` | 1 | state | 0 |
| `lem-cbc-regular-quotient-cone-augmentation` | 1 | state | 0 |
| `lem-cbc-ringed-open-scalar-limit-coherence` | 1 | state | 0 |
| `lem-coef-derived-tower-counit-projections` | 1 | state | 0 |
| `lem-coef-direct-image-hom-evaluation-square` | 1 | state | 0 |
| `lem-coef-exact-sections-reduction-unit` | 1 | state | 0 |
| `lem-coef-finite-compact-support-uniform-tor` | 1 | state | 0 |
| `lem-fd-local-frobenius-weil-morphism-naturality` | 1 | state | 0 |
| `lem-fix-open-scalar-tensor-normalization` | 1 | state | 0 |
| `lem-fix-proper-etale-origin-scalar-isomorphism` | 1 | state | 0 |
| `lem-kun-kflat-short-exact-quotient` | 1 | state | 0 |
| `lem-kun-lower-truncation-flat-model` | 1 | state | 0 |
| `lem-pd-ringed-tensor-adjunction-mate` | 1 | state | 0 |
| `lem-pe-completion-triangle-comparison` | 1 | state | 0 |
| `lem-pe-endomorphism-fibre-coordinate-calculus` | 1 | state | 0 |
| `lem-pe-endomorphism-fibre-double-cone` | 1 | state | 0 |
| `lem-pe-integral-completion-presentation` | 1 | state | 0 |
| `lem-per-continuous-coefficient-slice-normalization` | 1 | state | 0 |
| `lem-pod-fixed-pair-truncation-cohomology` | 1 | state | 0 |
| `lem-pur-adjoint-left-projection-action` | 1 | state | 0 |
| `lem-pur-affine-coordinate-support-stalk-continuity` | 1 | state | 0 |
| `lem-pur-classical-localization-triangle-transport` | 1 | state | 0 |
| `lem-pur-classical-support-counit-identification` | 1 | state | 0 |
| `lem-pur-clopen-finite-constructibility-bounds` | 1 | state | 0 |
| `lem-pur-clopen-roos-integral-descent` | 1 | state | 0 |
| `lem-pur-common-line-positive-scalar-powers` | 1 | state | 0 |
| `lem-pur-comparison-direct-image-resolution-mate` | 1 | state | 0 |
| `lem-pur-completed-coefficient-tensor-normalization` | 1 | state | 0 |
| `lem-pur-completed-line-tensor-coherence` | 1 | state | 0 |
| `lem-pur-completed-tensor-unit-insertion` | 1 | state | 0 |
| `lem-pur-composite-left-projection-action` | 1 | state | 0 |
| `lem-pur-composite-relative-tensor-action` | 1 | state | 0 |
| `lem-pur-concentrated-support-etale-transfer` | 1 | state | 0 |
| `lem-pur-coordinate-chart-finite-dimension-witness` | 1 | state | 0 |
| `lem-pur-derived-local-class-edge-comparison` | 1 | state | 0 |
| `lem-pur-derived-representable-transport` | 1 | state | 0 |
| `lem-pur-derived-tensor-additive-constraints` | 1 | state | 0 |
| `lem-pur-etale-direct-image-scalar-composition` | 1 | state | 0 |
| `lem-pur-etale-direct-image-scalar-exchange` | 1 | state | 0 |
| `lem-pur-etale-horizontal-double-counit` | 1 | state | 0 |
| `lem-pur-etale-kflat-support-comparison` | 1 | state | 0 |
| `lem-pur-etale-quotient-tensor-stalk-criterion` | 1 | state | 0 |
| `lem-pur-etale-sum-right-adjoint-coherence` | 1 | state | 0 |
| `lem-pur-etale-sum-right-adjoint-tensor` | 1 | state | 0 |
| `lem-pur-external-evaluation-transpose-natural` | 1 | state | 0 |
| `lem-pur-external-evaluation-two-shift-squares` | 1 | state | 0 |
| `lem-pur-factorized-pullback-square-pasting` | 1 | state | 0 |
| `lem-pur-finite-free-completion-exchange-coherence` | 1 | state | 0 |
| `lem-pur-finite-free-quotient-completion` | 1 | state | 0 |
| `lem-pur-finite-open-product-swap` | 1 | state | 0 |
| `lem-pur-finite-product-field-coefficient-descent` | 1 | state | 0 |
| `lem-pur-finite-proper-product-transpose` | 1 | state | 0 |
| `lem-pur-finite-pullback-localization-cohomology` | 1 | state | 0 |
| `lem-pur-finite-type-coordinate-support-orientation` | 1 | state | 0 |
| `lem-pur-global-hom-evaluation-flat-lift` | 1 | state | 0 |
| `lem-pur-good-truncation-exact-normalization` | 1 | state | 0 |
| `lem-pur-injective-tower-roos-shifts` | 1 | state | 0 |
| `lem-pur-integral-ambient-operation-models` | 1 | state | 0 |
| `lem-pur-inverse-image-scalar-unit-normalization` | 1 | state | 0 |
| `lem-pur-inverse-image-tensor-adjoint-test` | 1 | state | 0 |
| `lem-pur-lifted-external-evaluation-chain-model` | 1 | state | 0 |
| `lem-pur-normalized-operation-system-models` | 1 | state | 0 |
| `lem-pur-open-cover-cohomology-detection` | 1 | state | 0 |
| `lem-pur-open-left-projection-action` | 1 | state | 0 |
| `lem-pur-origin-class-projective-comparison` | 1 | state | 0 |
| `lem-pur-proetale-direct-image-global-evaluation` | 1 | state | 0 |
| `lem-pur-proetale-injective-support-global-model` | 1 | state | 0 |
| `lem-pur-proetale-support-global-boundary` | 1 | state | 0 |
| `lem-pur-quotient-diagram-projection-evaluation` | 1 | state | 0 |
| `lem-pur-quotient-expression-kflat-normalization` | 1 | state | 0 |
| `lem-pur-ringed-triple-resolution-formulas` | 1 | state | 0 |
| `lem-pur-semilinear-tensor-presentation-transport` | 1 | state | 0 |
| `lem-pur-sequence-adjoint-resolution-shifts` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-pur-strict-coefficient-comparison-calculus` | 1 | state | 0 |
| `lem-pur-support-comparison-common-injectives` | 1 | state | 0 |
| `lem-pur-support-comparison-section-model` | 1 | state | 0 |
| `lem-pur-support-quotient-pair-pullback` | 1 | state | 0 |
| `lem-pur-supported-constant-exchange-normalization` | 1 | state | 0 |
| `lem-pur-supported-hom-cocycle-normalization` | 1 | state | 0 |
| `lem-pur-tensor-action-trace-contraction` | 1 | state | 0 |
| `lem-pur-total-tensor-signed-coherence` | 1 | state | 0 |
| `lem-pur-tower-limit-transpose-normalization` | 1 | state | 0 |
| `lem-pur-unit-adjunct-tensor-action` | 1 | state | 0 |
| `lem-pur-unrestricted-frobenius-factorization` | 1 | state | 0 |
| `lem-sbc-common-stage-inverse-through-karoubi` | 1 | state | 0 |
| `lem-sbc-finite-stage-rational-exchange-coherence` | 1 | state | 0 |
| `lem-sbc-ringed-topos-sheaf-slice-derived-comparison` | 1 | state | 0 |
| `lem-sf-automorphism-completion-unit-comparison` | 1 | state | 0 |
| `lem-sf-bounded-epimorphic-top-derived-limit` | 1 | state | 0 |
| `lem-sf-cbc-direct-image-reduction-unit` | 1 | state | 0 |
| `lem-sf-cbc-localized-strict-tensor-descent` | 1 | state | 0 |
| `lem-sf-cbc-word-reconstruction-coherence` | 1 | state | 0 |
| `lem-sf-clopen-lisse-complete-localization` | 1 | state | 0 |
| `lem-sf-cochain-tensor-model-rigidity` | 1 | state | 0 |
| `lem-sf-complete-top-residue-cell-cone` | 1 | state | 0 |
| `lem-sf-completed-coefficient-free-resolution` | 1 | state | 0 |
| `lem-sf-completed-coefficient-pullback-linearity` | 1 | state | 0 |
| `lem-sf-completed-tensor-rational-naturality` | 1 | state | 0 |
| `lem-sf-derived-completed-tensor-bilinearity` | 1 | state | 0 |
| `lem-sf-etale-chart-left-compositor` | 1 | state | 0 |
| `lem-sf-etale-derived-pullback-stalk` | 1 | state | 0 |
| `lem-sf-etale-module-stalk-cohomology-test` | 1 | state | 0 |
| `lem-sf-open-quotient-koszul-completeness` | 1 | state | 0 |
| `lem-sf-open-roos-unit-adjunction` | 1 | state | 0 |
| `lem-sf-open-semilinear-tensor-model` | 1 | state | 0 |
| `lem-sf-perfect-tensor-roos-completion` | 1 | state | 0 |
| `lem-sf-point-ringed-evaluation-model` | 1 | state | 0 |
| `lem-sf-projective-cohomology-split-model` | 1 | state | 0 |
| `lem-sf-projective-top-cell-attachment` | 1 | state | 0 |
| `lem-sf-strict-dvr-reduction-triangles` | 1 | state | 0 |
| `lem-sf-tensor-comparison-localization-descent` | 1 | state | 0 |
| `lem-sfb-admissible-scalar-realization-exact` | 1 | state | 0 |
| `lem-sfb-closed-supported-scalar-comparison` | 1 | state | 0 |
| `lem-sfb-coefficient-diagram-regular-scalars` | 1 | state | 0 |
| `lem-sfb-condensed-localization-exact-cohomology` | 1 | state | 0 |
| `lem-sfb-constant-finite-free-presentation-extension` | 1 | state | 0 |
| `lem-sfb-constant-periodic-resolution-nonzero` | 1 | state | 0 |
| `lem-sfb-constructible-exact-scalar-triangulation` | 1 | state | 0 |
| `lem-sfb-continuous-frame-sheaf-comparison` | 1 | state | 0 |
| `lem-sfb-derived-degree-zero-abelian-criterion` | 1 | state | 0 |
| `lem-sfb-dvr-projective-complex-matrix-model` | 1 | state | 0 |
| `lem-sfb-etale-proetale-cube-flat-model` | 1 | state | 0 |
| `lem-sfb-etale-stalk-constant-complex-exactness` | 1 | state | 0 |
| `lem-sfb-etale-stalk-total-tensor-comparison` | 1 | state | 0 |
| `lem-sfb-finite-colimit-matrix-cokernels` | 1 | state | 0 |
| `lem-sfb-finite-flat-constructible-total-tensor` | 1 | state | 0 |
| `lem-sfb-finite-integral-condensed-resolution` | 1 | state | 0 |
| `lem-sfb-finite-open-direct-image-ctf` | 1 | state | 0 |
| `lem-sfb-finite-scalar-perfect-refinement` | 1 | state | 0 |
| `lem-sfb-flat-single-scalar-conventions` | 1 | state | 0 |
| `lem-sfb-fpqc-labelled-clopen-descent` | 1 | state | 0 |
| `lem-sfb-geometric-two-iso-scalar-pairing` | 1 | state | 0 |
| `lem-sfb-hom-flat-scalar-evaluation-model` | 1 | state | 0 |
| `lem-sfb-hom-kflat-chain-transpose` | 1 | state | 0 |
| `lem-sfb-hom-strict-numerator-transpose` | 1 | state | 0 |
| `lem-sfb-ind-finite-free-scalar-model` | 1 | state | 0 |
| `lem-sfb-integral-derived-extension-comparison` | 1 | state | 0 |
| `lem-sfb-integral-residue-class-triangle-closure` | 1 | state | 0 |
| `lem-sfb-kinjective-direct-image-open-word-model` | 1 | state | 0 |
| `lem-sfb-localized-ring-mate-graph-evaluation` | 1 | state | 0 |
| `lem-sfb-qcqs-proper-hull-tail-bound` | 1 | state | 0 |
| `lem-sfb-qlbar-point-abelian-colimit` | 1 | state | 0 |
| `lem-sfb-regular-scalar-extension-multiplication` | 1 | state | 0 |
| `lem-sfb-ring-isomorphism-tensor-transport` | 1 | state | 0 |
| `lem-sfb-ringed-hom-composition-model` | 1 | state | 0 |
| `lem-sfb-ringed-ordinary-evaluation-localization` | 1 | state | 0 |
| `lem-sfb-ringed-signed-bidual-localization` | 1 | state | 0 |
| `lem-sfb-ringed-site-bounded-evaluation-assembly` | 1 | state | 0 |
| `lem-sfb-scalar-perfect-dual-realization` | 1 | state | 0 |
| `lem-sfb-section-ring-lax-pushforward-coherence` | 1 | state | 0 |
| `lem-sfb-split-perfect-dual-tor-window` | 1 | state | 0 |
| `lem-sp-binary-cover-site-presentation` | 1 | state | 0 |
| `lem-sp-derived-split-fibre-projections` | 1 | state | 0 |
| `lem-sp-koszul-roos-projection-comparison` | 1 | state | 0 |
| `lem-sp-power-torsion-sheaf-limit-complete` | 1 | state | 0 |
| `lem-sp-semilinear-kflat-tower-model` | 1 | state | 0 |
| `lem-sp-subterminal-cover-module-ses` | 1 | state | 0 |
| `lem-sp-subterminal-derived-image-calculus` | 1 | state | 0 |
| `lem-sp-subterminal-module-local-calculus` | 1 | state | 0 |
| `lem-trf-completion-unit-strict-quotient-model` | 1 | state | 0 |
| `lem-trf-effective-comparison-realization-models` | 1 | state | 0 |
| `lem-trf-etale-shifted-line-normalized-descent` | 1 | state | 0 |
| `lem-trf-finite-ring-bundle-section-orientation` | 1 | state | 0 |
| `lem-trf-integral-comparison-counit-characterization` | 1 | state | 0 |
| `lem-trf-integral-composition-counit-images` | 1 | state | 0 |
| `lem-trf-isomorphism-multiplication-cone-descent` | 1 | state | 0 |
| `lem-trf-point-exact-derived-model` | 1 | state | 0 |
| `lem-trf-point-sheaf-insertion-calculus` | 1 | state | 0 |
| `lem-trf-quotient-system-mixed-coherence` | 1 | state | 0 |
| `lem-trf-section-coordinate-counit-normalization` | 1 | state | 0 |
| `lem-trf-section-exceptional-fibre-coherence` | 1 | state | 0 |
| `lem-trf-section-local-dualizing-comparisons` | 1 | state | 0 |
| `lem-trf-section-rees-base-change-etale` | 1 | state | 0 |
| `lem-trf-section-rees-noetherian-geometry` | 1 | state | 0 |
| `lem-trf-site-one-sided-tensor-normalization` | 1 | state | 0 |
| `lem-trf-smooth-section-centred-coordinates` | 1 | state | 0 |
| `lem-tw-ordinary-pullback-stratified-models` | 1 | state | 0 |
| `lem-weil-boundary-etale-adjunction-restriction` | 1 | state | 0 |
| `lem-weil-boundary-q-defining-composite-comparison` | 1 | state | 0 |
| `lem-weil-coefficient-complex-rationalization` | 1 | state | 0 |
| `lem-weil-isomorphism-comparison-natural` | 1 | state | 0 |
| `lem-weil-kinjective-total-derived-linear` | 1 | state | 0 |
| `lem-weil-pbc-affine-cohomology-etale-module-realization` | 1 | state | 0 |
| `lem-weil-pbc-completed-realization-derived-cohomology` | 1 | state | 0 |
| `lem-weil-pbc-derived-tensor-shift-descent` | 1 | state | 0 |
| `lem-weil-pbc-exact-square-derived-counit` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-completion-transport` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-constructible-scalar-transport` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-strict-tower-transport` | 1 | state | 0 |
| `lem-weil-pbc-fixed-tensor-localization-comparison` | 1 | state | 0 |
| `lem-weil-pbc-flat-scalar-tower-exchange` | 1 | state | 0 |
| `lem-weil-pbc-integral-model-open-closed-pieces` | 1 | state | 0 |
| `lem-weil-pbc-local-derived-restriction-comparisons` | 1 | state | 0 |
| `lem-weil-pbc-pair-functor-shift-coherence` | 1 | state | 0 |
| `lem-weil-pbc-raw-restricted-class-normalization` | 1 | state | 0 |
| `lem-weil-pbc-reflected-adjunction-coefficient-squares` | 1 | state | 0 |
| `lem-weil-pbc-scalar-perfect-cohomology-and-pid-models` | 1 | state | 0 |
| `lem-weil-pbc-total-tensor-homotopy-cone-signs` | 1 | state | 0 |
| `lem-weil-proetale-tor-interval-shift` | 1 | state | 0 |
| `lem-weil-proetale-tor-interval-triangle` | 1 | state | 0 |
| `lem-weil-roos-transition-homotopy` | 1 | state | 0 |
| `sk-lem-as-properties` | 1 | state | 0 |
| `sk-thm-picard-rr` | 1 | state | 0 |
| `lem-sf-constructible-canonical-completeness` | 2 | state | 0 |
| `lem-sf-open-reduction-adjunction-transport` | 2 | state | 0 |
| `lem-sfb-coefficient-mate-diagonal-graph` | 2 | state | 0 |
| `lem-trf-counit-realization-substitution` | 2 | state | 0 |
| `lem-weil-point-transformation-coefficient-descent` | 2 | state | 0 |

Not open yet: 354 nodes that below a finished node, not needed, 48 nodes that wait for stage 1 (statement downstream not grounded), 146 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (402)

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
| `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` | 5 | 10 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | proof | route |
| `Sheaf.Paper.AdicCoefficientDatumCompleted` | 6 | 6 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization` | 7 | 1 | proof | route |
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
| `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor` | - | 4 | proof | 2 |
| `Sheaf.Algebra.Homology.InternalHomLocalizationComparison` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
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
| `Sheaf.AlgebraicGeometry.SubfieldExtensionLocalPresentation` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedBelowHomTest` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.FormalExactProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.ClosedSupportBoundedContinuity` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CoefficientProjectionSquare` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | - | 1 | proof | 2 |
| `Sheaf.Paper.CommonStageCalculus` | - | 8 | proof | 2 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 13 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | - | 4 | proof | 2 |
| `Sheaf.Paper.ConstructibleTruncations` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedExchangeExactNormalization` | - | 3 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | - | 7 | proof | 2 |
| `Sheaf.Paper.ExactScalarPeriodicResolution` | - | 6 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.FiniteProEtalePushforwardConstructible` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteSubextensionsDirected` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.LocalFrobeniusTrace` | - | 5 | proof | 2 |
| `Sheaf.Paper.LocalIntegralPerfectModelCohomology` | - | 1 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | - | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | proof | 2 |
| `Sheaf.Paper.PointFibreEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.ReductionPullbackDerivedTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 13 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | - | 2 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatDvrScalarTensor` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatScalarCyclicResolution` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.KFlatScalarTowerRealization` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RHomColimitSourceTransport` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenFlatResolution` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.ScalarHomComparisonTower` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SitePerfectScalarHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.DirectImageScalarRestrictionCocycle` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFieldProEtaleDirectImage` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` | - | 7 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenRoosPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 3 |
| `Sheaf.CategoryTheory.AdicBasisLimit` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoherentCoconeNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.ExactTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DirectImageRoosNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.EquivalenceAdjunctionComparison` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.EquivariantCoequalizerComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactLinearKoszulFibre` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.InternalAbelianFiniteLimitCreation` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.JointAdjunctionModelEmbedding` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.LocalizedBasisCoefficients` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.LocallyPrescribedModulesSmall` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Monoidal.AdjunctionEquivalenceTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.MonoidalBalancingDiagrams` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedCompositorUnitNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorSquareMateFactorization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedCompleteTriangulated` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedPullbackLinear` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedDerivedPushforwardLinear` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarCoordinateLimitCriterion` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 3 |
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
| `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPerfectModelCompleteReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 3 |
| `Sheaf.Paper.AdicStratumCompletionUnit` | - | 2 | proof | 3 |
| `Sheaf.Paper.AmbTateRootProjectionReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | - | 7 | proof | 3 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedKoszulReductionRoosTriangle` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | - | 27 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | - | 44 | proof | 3 |
| `Sheaf.Paper.DerivedNakayama` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | - | 19 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientModelComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldLisseInternalHom` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldStratifiedGeneration` | - | 1 | proof | 3 |
| `Sheaf.Paper.FlatCommonQuotientReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | - | 7 | proof | 3 |
| `Sheaf.Paper.IntegralConstructibleHomSums` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCtfTriangulated` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelsExtensionClosed` | - | 1 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 4 | proof | 3 |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | - | 1 | proof | 3 |
| `Sheaf.Paper.OpenFiniteConstructibilityInterval` | - | 1 | proof | 3 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 9 | proof | 3 |
| `Sheaf.Paper.PbcDistinguishedDiagramLifting` | - | 1 | proof | 3 |
| `Sheaf.Paper.PerfectStrataUniformReductions` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 3 |
| `Sheaf.Paper.PrincipalReductionConeCalculus` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible` | - | 3 | proof | 3 |
| `Sheaf.Paper.ProEtaleScalarMateNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.QuotientScalarComparisonDescent` | - | 2 | proof | 3 |
| `Sheaf.Paper.RHomColimitCohomologyLadder` | - | 4 | proof | 3 |
| `Sheaf.Paper.RealizationScalarFunctor` | - | 1 | proof | 3 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 3 |
| `Sheaf.Paper.RingedPullbackHomEvaluationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 6 | proof | 3 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictPerfectRingedPullbackModel` | - | 3 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedTriangleMateIdentification` | - | 1 | proof | 3 |
| `Sheaf.Paper.SystemPushforwardRestrictionTransition` | - | 1 | proof | 3 |
| `Sheaf.Paper.TwoTermReductionCohomology` | - | 1 | proof | 3 |
| `Sheaf.Paper.WeilIndSheafCategory` | - | 8 | proof | 3 |
| `Sheaf.SixFunctors.FiniteProperClassicalTruncation` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarConjugateNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 7 | proof | 3 |
| `Sheaf.TraceFormula.PointTransportComposition` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 13 | 3 | proof | 4 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatConstantScalarMono` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` | - | 6 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RoosConeCalculus` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SuccessiveQuotientFlatComplexSequence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteConstantMapNaturality` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FlatConstructibleTensor` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.OpenSourceComposition` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarPresentationCokernel` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange` | - | 7 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AdditiveLocalizationDescent` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.AdjointEquivalenceConjugation` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ClosedEvaluationDualCriterion` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.CofinalRoosRestriction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ExactAdjointTowerModels` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveExactSquareComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.KInjectiveFiberTriangleComparison` | - | 3 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjectCokernelAction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.ModuleObjects.KernelStructure` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.Monoidal.UnitTensorBraiding` | - | 2 | proof | 4 |
| `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingLocalizationSheafification` | - | 5 | proof | 4 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.Sites.ToposComplementFactorization` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompatibleCoefficientTower` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantDerivedLimitResolutionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 4 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedTowerEvaluationNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleOpenScalarExchange` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleSumCoefficientComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | - | 3 | proof | 4 |
| `Sheaf.Paper.FiniteCompactSiteCoherence` | - | 11 | proof | 4 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | - | 5 | proof | 4 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | proof | 4 |
| `Sheaf.Paper.OpenLocalizedCounitComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.OpenScalarSiteCoherence` | - | 8 | proof | 4 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 4 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurAdicLineSystemBaseChange` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityFiniteOpenIntervalDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 4 |
| `Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedCoefficientPullbackComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSlicePullbackMateNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 7 | proof | 4 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 4 |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | proof | 4 |
| `Sheaf.Paper.SheafTensorIdealQuotient` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratumCompletionUnitRestriction` | - | 11 | proof | 4 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 4 |
| `Sheaf.ProperBaseChange.SingletonSiteModuleComparison` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleOpenScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalAmplitude` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalBoundedSums` | - | 6 | proof | 4 |
| `Sheaf.SixFunctors.FiniteProperClassicalNeighborhoodVanishing` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.EtaleClosedComplementSets` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedTensorComplexConstraints` | 5 | 1 | proof | 5 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 5 |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | 9 | 1 | proof | 5 |
| `Sheaf.RingTheory.ModuleLocalizationFilteredColimit` | 10 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.BalancedTensorChain` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SmoothAdmissibleCoordinateCover` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor` | - | 5 | proof | 5 |
| `Sheaf.CategoryTheory.FiniteRingActionLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.NormalizedAdjunctionSquareTranspose` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SheafTensorUnitComparison` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.Sites.ClosedComplementSiteConstruction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation` | - | 1 | proof | 5 |
| `Sheaf.NumberTheory.Padics.FiniteSumLattice` | - | 1 | proof | 5 |
| `Sheaf.Paper.ConstructibleLocalizingDetermination` | - | 1 | proof | 5 |
| `Sheaf.Paper.ContinuousLatticeSum` | - | 1 | proof | 5 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 5 |
| `Sheaf.Paper.GeometricStalkPerfect` | - | 4 | proof | 5 |
| `Sheaf.Paper.IntegralLineReductionRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.LatticePullback` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackComposition` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.CoherentRightAdjointComparisons` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.DerivedCategory.UnboundedKFlatResolution` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | - | 1 | proof | 6 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | - | 1 | proof | 6 |
| `Sheaf.Topology.TopologicalBasisLiftSection` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.RingedDerivedCompositionComparison` | 15 | 1 | proof | 7 |
| `Sheaf.SixFunctors.RingedDerivedTwoIsoComparison` | 15 | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels` | - | 2 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.ComparisonGlobalResolutionModel` | - | 1 | proof | 7 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 7 |
| `Sheaf.Paper.LocalModelTorBoundDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.TAdmissibleDualizableTruncations` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SubcategoryLeftResolution` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality` | - | 4 | proof | 8 |
| `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined` | - | 1 | proof | 8 |
| `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact` | - | 1 | proof | 8 |
| `Sheaf.RingTheory.ProEtale.HenselianClosedLift` | - | 1 | proof | 8 |
| `Sheaf.RingTheory.HenselianWStrictLocalInvariance` | - | 1 | proof | 9 |
| `Sheaf.RingTheory.HenselianSmoothAlgebraLifting` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf` | - | 1 | proof | 18 |

## Stage 3: waiting for statements of dependencies (73)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | `lem-zl-constant-geometric-stalk-unit` |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 2 | `lem-sfb-qlbar-point-abelian-colimit` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | 4 | 2 | `lem-sfb-integral-derived-extension-comparison` |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | `lem-sfb-hom-strict-numerator-transpose` |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | - | 2 | `lem-sf-locally-closed-closure-adjoint-realization` |
| `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting` | - | 1 | `lem-sfb-section-ring-lax-pushforward-coherence` |
| `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts` | - | 1 | `lem-sfb-qcqs-proper-hull-tail-bound` |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | - | 1 | `lem-pur-closed-finite-adjoint-counit-transport` |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | - | 1 | `lem-coef-closed-identity-open-hom-normalization` |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | `lem-weil-pbc-affine-cohomology-etale-module-realization` |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | - | 1 | `lem-per-adic-common-stage-truncations` |
| `Sheaf.Paper.BoundaryDualizingComposition` | - | 1 | `lem-weil-boundary-etale-adjunction-restriction` |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | - | 1 | `lem-sf-boundary-bounded-tensor-comparison` |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | - | 1 | `lem-weil-boundary-q-defining-composite-comparison` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-signed-line-derived-base-change` |
| `Sheaf.Paper.CoefTowerCoaugmentation` | - | 1 | `lem-coef-derived-tower-counit-projections` |
| `Sheaf.Paper.CompactSupportReductionTower` | - | 1 | `lem-pur-sequence-site-completion-projection` |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | - | 1 | `lem-weil-kinjective-total-derived-linear` |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | `lem-cbc-completed-ring-strict-finite-exchange` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-pulled-reduction-normalization-comparison` |
| `Sheaf.Paper.CompositeIntegrationCounit` | - | 6 | `lem-pur-tensor-action-trace-contraction` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | - | 1 | `lem-per-constructible-rational-hom-comparison` |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | - | 1 | `lem-sfb-kinjective-direct-image-open-word-model` |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | `lem-pe-completion-triangle-comparison` |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | `lem-sp-proetale-scalar-tensor-normalization` |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | - | 3 | `lem-fix-open-scalar-tensor-normalization` |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | - | 1 | `lem-pur-finite-proper-product-transpose` |
| `Sheaf.Paper.FiniteRingSectionDeformation` | - | 11 | `lem-trf-smooth-section-centred-coordinates` |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | - | 1 | `lem-coef-finite-compact-support-uniform-tor` |
| `Sheaf.Paper.IntegralConstantModelHeart` | - | 1 | `lem-sfb-integral-residue-class-triangle-closure` |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | - | 1 | `lem-coef-residue-controlled-finite-homs` |
| `Sheaf.Paper.IntegralCriterionReductions` | - | 8 | `lem-pe-integral-completion-presentation` |
| `Sheaf.Paper.IntegralHeartLocalModel` | - | 9 | `lem-sfb-dvr-projective-complex-matrix-model` |
| `Sheaf.Paper.IntegralModelsOperations` | - | 1 | `lem-sfb-scalar-model-immersion-extension` |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | `lem-pur-integral-ambient-operation-models` |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | - | 13 | `lem-trf-point-system-transport-descent` |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | - | 1 | `lem-trf-point-transport-strict-quotient` |
| `Sheaf.Paper.IntegralTensorPullback` | - | 8 | `lem-sfb-integral-bounded-stratum-base-change` |
| `Sheaf.Paper.IntegralTwistBaseChange` | - | 1 | `lem-pur-common-line-positive-scalar-powers` |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | - | 4 | `lem-sfb-admissible-scalar-realization-exact` |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | - | 1 | `lem-weil-pbc-lisse-lattice-reduced-open` |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | - | 1 | `lem-sfb-stratified-tor-interval-devissage` |
| `Sheaf.Paper.ModuleDerivedCompositorCoherence` | - | 4 | `lem-sfb-section-ring-lax-pushforward-coherence` |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | `lem-pd-section-derived-open-adjunction-normalization` |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | - | 3 | `lem-pd-ringed-tensor-adjunction-mate` |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | - | 1 | `lem-pur-completed-coefficient-tensor-normalization` |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | `lem-pur-injective-tower-roos-shifts` |
| `Sheaf.Paper.PurityConventions` | - | 11 | `sk-def-sf-operations` |
| `Sheaf.Paper.PurityGeneralAdmissibility` | - | 1 | `lem-pur-affine-chart-exceptional-identification` |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | - | 1 | `lem-fd-integral-identity-rational-equivalence` |
| `Sheaf.Paper.ReductionOpenEtaleOrigin` | - | 1 | `lem-fix-open-scalar-tensor-normalization` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `lem-pur-finite-type-coordinate-support-orientation` |
| `Sheaf.Paper.RingedSitePerfectProjectionFormula` | - | 1 | `lem-sbc-ringed-topos-sheaf-slice-derived-comparison` |
| `Sheaf.Paper.ScalarCompletionAssociator` | - | 1 | `lem-pur-finite-free-completion-exchange-coherence` |
| `Sheaf.Paper.SectionOrdinaryOplaxNormalization` | - | 1 | `lem-pd-ringed-tensor-adjunction-mate` |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | - | 2 | `lem-sf-compact-support-proper-image-tower` |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | - | 4 | `lem-sp-ell-coefficient-fiber` |
| `Sheaf.Paper.StratifiedLatticeRank` | - | 1 | `lem-sfb-continuous-coefficient-free-rank` |
| `Sheaf.Paper.StrictQuotientExchangeUnitEquation` | - | 1 | `lem-weil-pbc-constant-tower-pushforward-normalization` |
| `Sheaf.Paper.TateTwistLocallyFree` | - | 1 | `lem-pur-completed-line-tensor-coherence` |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | - | 1 | `lem-sfb-lattice-supported-hom-reduction-tower` |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | - | 1 | `lem-pur-shifted-tate-unit-scalar-coherence` |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | - | 1 | `lem-pur-finite-site-counit-projection-transport` |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | `lem-sp-signed-tate-coefficient-exponent-normalization` |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | - | 1 | `lem-sfb-finite-open-direct-image-ctf` |
| `Sheaf.SixFunctors.AdmissibleTensorConstructibility` | - | 1 | `lem-sfb-ring-isomorphism-tensor-transport` |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | - | 1 | `lem-sfb-identity-open-underived-square-normalization` |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | `lem-sfb-lattice-subquotient-filtration` |
| `Sheaf.SixFunctors.OpenFactorCoherence` | - | 1 | `lem-sf-open-exchange-roos-restriction` |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | `lem-sfb-closed-supported-scalar-comparison` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `lem-sfb-condensed-bounded-hom-continuity` |

## Stage 3: held for an open upstream PR (19)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
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
