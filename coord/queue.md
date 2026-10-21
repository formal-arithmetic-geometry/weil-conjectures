# Work queue

186 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (13 clusters, 1358 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 27, stage 3 353 items.

## Stage 1: nodes to split (102)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `prop-weil-pbc-qbar-condensed-two-colimit` | 0 | rests_on_sorry |
| `lem-pd-module-ringed-topos-derived-comparison` | 1 | none |
| `prop-weil-pbc-scalar-extension` | 1 | none |
| `def-pd-proetale-section-module-functors` | 2 | none |
| `lem-weil-pbc-constant-completion-equivalence` | 2 | none |
| `lem-weil-pbc-integral-stratified-perfect-characterization` | 2 | none |
| `lem-weil-pbc-ringed-projection-mate-exact` | 2 | none |
| `lemma-weil-pbc-perfect-projection-formula` | 2 | none |
| `prop-weil-pbc-direct-image-limits` | 2 | none |
| `lem-pur-finite-coefficient-adjoint-comparisons` | 3 | none |
| `lem-weil-pbc-comparison-injective-acyclicity` | 3 | rests_on_sorry |
| `lem-weil-pbc-condensed-e-realization` | 3 | none |
| `lem-weil-pbc-ringed-projection-restriction` | 3 | none |
| `lem-weil-pbc-lisse-e-constructible-integral-lattice` | 4 | none |
| `lemma-weil-pbc-completed-pullback-reduction` | 4 | none |
| `sk-thm-properbasechange` | 4 | rests_on_sorry |
| `lem-sbc-completed-operations-linear-natural-exchange` | 5 | none |
| `lem-weil-pbc-scalar-localization-sheaf-exact` | 5 | none |
| `lem-weil-pbc-coherent-affine-base-change-edge-naturality` | 17 | none |
| `lem-sfb-filtered-ring-object-cocone-colimit` | 1001 | none |
| `lem-weil-finite-free-completed-scalar-comparison` | 1001 | none |
| `lem-sf-compact-support-restriction-of-scalars` | 1002 | none |
| `lem-sf-integral-compact-support-constructible` | 1002 | none |
| `lem-weil-compact-support-reduction-tower-functor` | 1002 | none |
| `lem-weil-integral-scalar-extension-well-defined` | 1002 | none |
| `det-sf-comp-composition-interchange` | 1004 | none |
| `lem-pur-completed-coefficient-pushforward-comparison` | 1004 | none |
| `det-def-sp-tate-twist-locally-free` | 2000 | none |
| `lem-sf-integral-direct-image-constructible` | 2002 | none |
| `det-prop-sfb-cartesian-coefficients-twists` | 2003 | none |
| `det-sf-comp-coherence-cocycle` | 2003 | none |
| `lem-cbc-completed-extension-zero-comparison` | 2003 | none |
| `lem-cbc-adic-pullback-presentation-transport` | 2004 | none |
| `lem-cbc-ringed-open-extension-products` | 2004 | none |
| `lem-pe-comparison-injective-left-modules-acyclic` | 2004 | sorry_here |
| `det-sf-existence-brown` | 2005 | none |
| `lem-pur-etale-compact-scalar-coherence` | 2005 | none |
| `lem-fix-operation-reduction` | 3002 | none |
| `lem-coef-derived-system-evaluation-calculus` | 5002 | none |
| `lem-fix-compact-support-coefficient-change` | 5003 | none |
| `lem-sf-module-object-ordinary-coefficient-equivalence` | 5004 | none |
| `sk-prop-sf-rf-shriek-preservation` | 5004 | rests_on_sorry |
| `det-def-sfb-filtered-two-colimit-characterization` | - | none |
| `det-thm-sfb-proper-base-change-rational` | - | none |
| `def-sfb-module-linear-open-lower-shriek` | - | rests_on_sorry |
| `def-sfb-module-open-lower-shriek` | - | rests_on_sorry |
| `det-lem-integral-models-generators` | - | none |
| `det-lem-integral-models-operations` | - | none |
| `det-prop-scalar-six-pullback` | - | none |
| `det-prop-sfb-cartesian-coefficients-finite-free` | - | none |
| `det-thm-sfb-proper-base-change-integral` | - | none |
| `lem-pur-integral-operations-scalar-extension` | - | none |
| `lem-sfb-dc-lower-star-preserves` | - | none |
| `lem-sfb-dc-open-lower-shriek-preserves` | - | none |
| `lem-sfb-dc-upper-star-preserves` | - | none |
| `lem-sfb-extend-to-qlbar-constructible` | - | sorry_here |
| `lem-sfb-internal-module-operations-transport` | - | none |
| `sk-def-sfb-module-lower-shriek` | - | sorry_here |
| `sk-prop-sfb-cartesian-coefficients` | - | rests_on_sorry |
| `det-def-localizing-closure-ctf-equals-bc` | - | none |
| `det-lem-coefficient-heart-filtration` | - | none |
| `det-pe-derived-nakayama-first-reduction` | - | none |
| `det-prop-integral-criterion-reductions` | - | none |
| `det-sp-reduction-direct-image` | - | none |
| `det-sp-reduction-exceptional` | - | none |
| `det-sp-scalar-extension-functor` | - | none |
| `det-thm-sfb-proper-base-change-finite` | - | none |
| `lem-sfb-dc-hom-small-coefficients` | - | none |
| `lem-sfb-qlbar-tail-module-colimit` | - | none |
| `prop-sfb-module-left-derived-upper-star-comp` | - | none |
| `sk-def-pe-derived-completion` | - | none |
| `sk-lem-integral-models` | - | none |
| `sk-lem-stratified-lattice` | - | none |
| `det-lem-integral-models-stacks` | - | none |
| `det-pe-derived-nakayama-resolution` | - | none |
| `lem-sf-semilinear-proper-open-mate-pasting` | - | none |
| `lem-sfb-abelian-functorial-flat-resolution` | - | none |
| `lem-sfb-adic-constructibility-predicate-comparison` | - | none |
| `lem-sfb-condensed-subfield-basis` | - | none |
| `lem-sfb-constructible-cocone-obj` | - | sorry_here |
| `lem-sfb-constructible-internal-hom-continuity` | - | none |
| `lem-sfb-dc-hom-filtered-colimit` | - | none |
| `lem-sfb-finite-field-internal-hom-finiteness` | - | none |
| `lem-sfb-finite-free-scalar-coordinates` | - | none |
| `lem-sfb-integral-cohomological-adic-criterion` | - | none |
| `lem-sfb-monoidal-finite-free-transport` | - | none |
| `lem-sfb-pullback-constant-model-constructible` | - | none |
| `lem-sfb-sheaf-pushforward-generator-comparison` | - | none |
| `lem-sp-direct-image-change-ring-transpose` | - | none |
| `lem-sp-et-proet-coefficient-compatibility` | - | none |
| `thm-sfb-extend-scalars-localization` | - | sorry_here |
| `det-ctf-finite-proper-localizing` | - | none |
| `lem-sfb-adic-stratified-perfect` | - | none |
| `lem-sfb-constructible-cocone-hom-surj` | - | sorry_here |
| `lem-sfb-etale-proetale-scalar-mate` | - | none |
| `lem-sfb-exact-derived-composition` | - | none |
| `lem-sfb-exact-derived-natural-iso` | - | none |
| `lem-sfb-internal-scalar-extension-finite-presentation` | - | none |
| `lem-sfb-module-object-ringed-site-derived-comparison` | - | none |
| `lem-sp-acyclic-flat-proper-coefficient-model` | - | none |
| `lem-sp-varying-ring-proper-open-pasting` | - | none |
| `det-brown-hypotheses-small` | - | none |

## Stage 2: nodes to state (0)


Not open yet: 301 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up), 15 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (61)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 10 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 10 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | 1 | 2 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` | 2 | 10 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 4 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 5 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SingleProperOpenFiniteNormalization` | 8 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.StrictTowerAlphaEvaluation` | 9 | 1 | proof | route |
| `Sheaf.Paper.FiniteComparisonPresentation` | 9 | 1 | proof | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 1 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 4 | 15 | proof | 2 |
| `Sheaf.CategoryTheory.SheafificationTensorLocalIso` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 7 | 11 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | 8 | 7 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | 9 | 14 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 4 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.Paper.DerivedNakayamaResolution` | 5 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | 11 | 1 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | 11 | 3 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedProjectionCoherence` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 8 | 3 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | 9 | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |

## Stage 3: waiting for statements of dependencies (14)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | `lem-sfb-adic-constructibility-predicate-comparison` |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 2 | `lem-sfb-filtered-ring-object-cocone-colimit` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | 5 | 5 | `det-def-sfb-filtered-two-colimit-characterization` |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | 6 | 1 | `lem-cbc-ringed-open-extension-products` |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | 6 | 1 | `det-prop-diagonal-tower-coefficients` |
| `Sheaf.Targets.AffineSpaceRationalLine` | 8 | 1 | `det-prop-p1-adjunction-rational-triangle` |
| `Sheaf.Paper.DlConstructibleFibresExact` | - | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 8 | `lem-pur-system-level-projection-formula-coherence` |
| `Sheaf.Paper.FiniteTorStability` | - | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `sk-thm-sf-tensor-hom` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | - | 8 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SixFunctors.RationalOperations` | - | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SmoothPurity.NormalizedWitness` | - | 1 | `lem-pur-condensed-exceptional-reconstruction` |

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
