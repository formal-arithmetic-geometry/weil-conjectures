# Work queue

586 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (24 clusters, 1028 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.SitePerfectComplex` | 1 |  | error: Sheaf/Paper/SitePerfectComplex.lean:122:10: failed to synthesize instance of type class |
| `Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.SixFunctors.ClosedImmersionTensorProjection` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.WeilTensorProduct` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FormalClosedSupport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | 1 |  | error: Sheaf/Paper/ExtensionZeroStratifiedPerfect.lean:87:9: Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.ReductionOpenEtaleOrigin` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 89, stage 3 21 items.

## Stage 1: nodes to split (18)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-qcqs-rational-integral-localizing-generators` | 2006 | none |
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-lisse-lattice-potential-kummer-tameness` | 4010 | none |
| `lem-sfb-tame-inertia-continuous-koszul` | 4010 | none |
| `lem-sfb-complete-group-forgetful-automorphisms` | 4011 | none |
| `lem-sfb-condensed-derived-invariant-bar` | 4011 | none |
| `lem-sfb-condensed-product-action-inflation` | 4011 | none |
| `lem-sfb-derived-cech-image-totalization` | 4011 | none |
| `lem-sfb-gabber-global-snc-alteration` | 4011 | none |
| `lem-sfb-partial-kummer-boundary-unit-model` | 4011 | none |
| `lem-sfb-pointed-finite-etale-limit-cover` | 4011 | none |
| `lem-sfb-prime-to-ell-linear-image-finite` | 4011 | none |
| `lem-sfb-root-tower-boundary-acyclicity` | 4011 | none |
| `lem-sfb-spectral-clopen-component-homeomorphism` | 4011 | none |
| `lem-sfb-supported-finite-stage-topology-defect` | 4011 | none |
| `lem-sfb-tame-root-tower-extension` | 4011 | none |
| `lem-sfb-totally-disconnected-coefficient-realization` | 4011 | none |
| `def-per-support-condition` | - | none |

## Stage 2: nodes to state (35)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `sk-d-real-weights` | 1 | state | 0 |
| `det-sp-rational-localized-hom` | 1 | state | 6 |
| `lem-tw-lisse-rational-realization` | 1 | state | 5 |
| `lem-sfb-integral-quotient-direct-image-comparison` | 1 | state | 2 |
| `lem-per-adic-stratified-pullback-texact` | 1 | state | 1 |
| `lem-sfb-field-separable-cech-coordinates` | 1 | state | 1 |
| `lem-weil-point-derived-sections-tensor-descent` | 1 | state | 1 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-coef-enriched-sequence-projection-formula` | 1 | state | 0 |
| `lem-fd-common-stage-comparison-descent` | 1 | state | 0 |
| `lem-fd-frobenius-fixed-pair-comparison` | 1 | state | 0 |
| `lem-fd-whole-tower-integral-pullback-comparison` | 1 | state | 0 |
| `lem-per-rational-realization-finite-cone-models` | 1 | state | 0 |
| `lem-pod-fixed-pair-truncation-cohomology` | 1 | state | 0 |
| `lem-pur-affine-coordinate-support-stalk-continuity` | 1 | state | 0 |
| `lem-pur-concentrated-support-etale-transfer` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-sf-cbc-localized-strict-tensor-descent` | 1 | state | 0 |
| `lem-sf-open-exchange-roos-restriction` | 1 | state | 0 |
| `lem-sf-open-roos-unit-adjunction` | 1 | state | 0 |
| `lem-sf-tensor-comparison-localization-descent` | 1 | state | 0 |
| `lem-sfb-constructible-algcl-topology-comparison` | 1 | state | 0 |
| `lem-sfb-integral-ambient-tower-comparison` | 1 | state | 0 |
| `lem-sfb-integral-general-lfp-hom-finiteness` | 1 | state | 0 |
| `lem-sfb-integral-pullback-strict-roos-normalization` | 1 | state | 0 |
| `lem-sfb-nested-open-regular-alteration` | 1 | state | 0 |
| `lem-sfb-normal-generic-continuous-sections` | 1 | state | 0 |
| `lem-sfb-qlbar-internal-hom-coefficient-comparison` | 1 | state | 0 |
| `lem-sfb-tame-stratum-kummer-descent` | 1 | state | 0 |
| `lem-sfb-transverse-tame-open-shriek-exchange` | 1 | state | 0 |
| `lem-sp-cofinal-finite-reduction-constructibility` | 1 | state | 0 |
| `lem-sp-supported-etale-tensor-origin` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-strict-tower-transport` | 1 | state | 0 |
| `lem-zl-weil-generic-lissity` | 1 | state | 0 |

Not open yet: 374 nodes that below a finished node, not needed, 111 nodes that wait for a statement dependency (bottom-up), 17 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (501)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 9 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | repair | route |
| `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` | 6 | 1 | repair | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | repair | route |
| `Sheaf.CategoryTheory.ElementRestrictionHom` | 9 | 1 | repair | route |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | 3 | 1 | disputed | 2 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | - | 1 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison` | - | 1 | proof | 1 |
| `Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicConstructibilityPredicateComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | - | 1 | proof | 1 |
| `Sheaf.Paper.FiniteDiscreteConstructibleModel` | - | 1 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | - | 21 | proof | 1 |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralConstructibleCompletionBridge` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralGeneralLfpHomInversion` | - | 1 | proof | 1 |
| `Sheaf.Paper.LocalizedDirectImageComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | proof | 1 |
| `Sheaf.Paper.NormedCoefficientRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.QlbarDirectImageComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.StratifiedTorIntervalDevissage` | - | 1 | proof | 1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | proof | 1 |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 4 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 11 | 2 | proof | 2 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.CommonStageKaroubiInverse` | - | 9 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicStratifiedPerfect` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbTateRootProjectionReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.BoundedFiniteModelGeneration` | - | 1 | proof | 2 |
| `Sheaf.Paper.CartesianCoefficients` | - | 2 | proof | 2 |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientProjectionSquare` | - | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportReductionTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 11 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | - | 4 | proof | 2 |
| `Sheaf.Paper.ConstructibleTruncations` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedExchangeExactNormalization` | - | 3 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | - | 7 | proof | 2 |
| `Sheaf.Paper.EtaleWeilSheafEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | - | 2 | proof | 2 |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.FiniteLocalModelRHomContinuity` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteProperBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteStageRationalExchangeCoherence` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.IdentityOpenDerivedRestriction` | - | 3 | proof | 2 |
| `Sheaf.Paper.IntegralCriterionReductions` | - | 8 | proof | 2 |
| `Sheaf.Paper.IntegralModels` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralModelsOperations` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | - | 1 | proof | 2 |
| `Sheaf.Paper.LocalFrobeniusTrace` | - | 5 | proof | 2 |
| `Sheaf.Paper.ModuleDerivedCompositorCoherence` | - | 4 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.NormalizedOpenRefinementCoherence` | - | 5 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | - | 3 | proof | 2 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` | - | 1 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 2 |
| `Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SectionDerivedPushpullNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.SectionDerivedTensorNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SectionOrdinaryOplaxNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | - | 2 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 1 | proof | 2 |
| `Sheaf.Paper.TopologicalStratifiedLisseLattices` | - | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.ScalarSixPullback` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 3 |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 13 | 3 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.OneKFlatChainTranspose` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SitePerfectScalarHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.StrictScalarHomChain` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale` | - | 4 | proof | 3 |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.NormalizedRoosShiftComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.UnitPowerCompleteness` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPerfectModelCompleteReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 3 |
| `Sheaf.Paper.AdicStratumCompletionUnit` | - | 2 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.BoundaryBoundedTensorComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.BoundaryQDefiningCompositeComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ClopenRoosIntegralDescent` | - | 12 | proof | 3 |
| `Sheaf.Paper.CoefficientHeart` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedKoszulReductionRoosTriangle` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedOpenFiniteEtaleOrigins` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | - | 10 | proof | 3 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | - | 27 | proof | 3 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 2 | proof | 3 |
| `Sheaf.Paper.CompletionTriangleComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 6 | proof | 3 |
| `Sheaf.Paper.CondensedLocalizationHom` | - | 3 | proof | 3 |
| `Sheaf.Paper.ConstantScalarStrictUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | - | 44 | proof | 3 |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedNakayama` | - | 1 | proof | 3 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | - | 19 | proof | 3 |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients` | - | 1 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.FdIntegralIdentityRationalEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteClopenConstructibilityBounds` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientModelComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldLisseInternalHom` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeConstructibleScalarTransport` | - | 2 | proof | 3 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | - | 12 | proof | 3 |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | - | 7 | proof | 3 |
| `Sheaf.Paper.IntegralAmbientOperationModels` | - | 4 | proof | 3 |
| `Sheaf.Paper.IntegralCoefficientPresentationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | - | 7 | proof | 3 |
| `Sheaf.Paper.IntegralConstructibleHomSums` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralLocalizationHomColimit` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelOpenClosedPieces` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelsExtensionClosed` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralStratumHomFormula` | - | 2 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.LatticeSubquotientFiltration` | - | 1 | proof | 3 |
| `Sheaf.Paper.LisseLatticeReducedOpen` | - | 1 | proof | 3 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 4 | proof | 3 |
| `Sheaf.Paper.PerAdicCommonStageTruncations` | - | 1 | proof | 3 |
| `Sheaf.Paper.PerfectStrataUniformReductions` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | - | 1 | proof | 3 |
| `Sheaf.Paper.PrincipalKoszulStrictReplacement` | - | 6 | proof | 3 |
| `Sheaf.Paper.PrincipalReductionConeCalculus` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleScalarMateNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.ProperEtaleOriginScalarIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.QuotientSystemMixedCoherence` | - | 3 | proof | 3 |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | - | 1 | proof | 3 |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | - | 2 | proof | 3 |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | - | 11 | proof | 3 |
| `Sheaf.Paper.RationalRealizationTensorComparison` | - | 2 | proof | 3 |
| `Sheaf.Paper.RationalStratumIntegralModels` | - | 2 | proof | 3 |
| `Sheaf.Paper.RealizationAdjointComparisons` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealizationCompletedPull` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealizationLocalizedPush` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealizationScalarFunctor` | - | 1 | proof | 3 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 3 |
| `Sheaf.Paper.RingedTensorAdjunctionMate` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicUnitComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ScalarModelImmersionExtension` | - | 1 | proof | 3 |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | - | 13 | proof | 3 |
| `Sheaf.Paper.SequenceSiteCompletionProjection` | - | 1 | proof | 3 |
| `Sheaf.Paper.SequenceSiteOpenExtension` | - | 1 | proof | 3 |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | proof | 3 |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.StratifiedLatticeRank` | - | 1 | proof | 3 |
| `Sheaf.Paper.StrictQuotientExchangeUnitEquation` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.Paper.SystemPushforwardRestrictionTransition` | - | 1 | proof | 3 |
| `Sheaf.Paper.TwoTermReductionCohomology` | - | 1 | proof | 3 |
| `Sheaf.Paper.WeilIndSheafCategory` | - | 8 | proof | 3 |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | proof | 3 |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarConjugateNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation` | - | 2 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 7 | proof | 3 |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | - | 1 | proof | 3 |
| `Sheaf.TraceFormula.PointTransportComposition` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 4 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 4 |
| `Sheaf.Paper.PbcActualScalarPullback` | 15 | 2 | proof | 4 |
| `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.ExactPullbackSignedComparison` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | - | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization` | - | 5 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FlatConstructibleTensor` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare` | - | 5 | proof | 4 |
| `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ScalarPresentationCokernel` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | - | 6 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange` | - | 7 | proof | 4 |
| `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.InjectiveTowerRoosShifts` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.TowerLimitTransposeNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientHeartFiltration` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompactSupportCoefficientChange` | - | 8 | proof | 4 |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompleteTopResidueCellCone` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedFiniteExchangeCoordinates` | - | 2 | proof | 4 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | - | 23 | proof | 4 |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | - | 2 | proof | 4 |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | - | 8 | proof | 4 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 4 |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedTensorUnitInsertion` | - | 1 | proof | 4 |
| `Sheaf.Paper.CondensedBoundedHomContinuity` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantDerivedLimitResolutionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 4 |
| `Sheaf.Paper.ContinuousCoefficientFreeRank` | - | 1 | proof | 4 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedCompletedTensorBilinearity` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleDirectImageScalarComposition` | - | 2 | proof | 4 |
| `Sheaf.Paper.EtaleSumCoefficientComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExactSectionsReductionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | - | 3 | proof | 4 |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 4 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | - | 5 | proof | 4 |
| `Sheaf.Paper.IntegralConstructibleHeart` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | proof | 4 |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | - | 1 | proof | 4 |
| `Sheaf.Paper.IsomorphismScalarTensorKFlatModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | - | 1 | proof | 4 |
| `Sheaf.Paper.NormalizedOperationSystemModels` | - | 1 | proof | 4 |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | - | 1 | proof | 4 |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | - | 1 | proof | 4 |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | - | 1 | proof | 4 |
| `Sheaf.Paper.OpenScalarSiteCoherence` | - | 8 | proof | 4 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 4 |
| `Sheaf.Paper.OrdinaryPullbackStratifiedModels` | - | 10 | proof | 4 |
| `Sheaf.Paper.PbcAutomorphismTransport` | - | 13 | proof | 4 |
| `Sheaf.Paper.PerfectQuotientExchangeNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointExactDerivedModel` | - | 5 | proof | 4 |
| `Sheaf.Paper.PointFiniteFreeSectionsTensor` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectionSectionNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectiveCohomologySplitModel` | - | 3 | proof | 4 |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityFiniteOpenIntervalDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 4 |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | - | 1 | proof | 4 |
| `Sheaf.Paper.QuotientDiagramProjectionEvaluation` | - | 1 | proof | 4 |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedOpenScalarLimitCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 7 | proof | 4 |
| `Sheaf.Paper.SfClopenLisseCompleteLocalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SfCompletedPullbackMateFactorization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SfExactPullbackCounitNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SignedTateCoefficientExponentNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | - | 1 | proof | 4 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratifiedDualizableBounded` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratifiedDualizableHomContinuity` | - | 5 | proof | 4 |
| `Sheaf.Paper.StratifiedLattice` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratumCompletionUnitRestriction` | - | 11 | proof | 4 |
| `Sheaf.Paper.StrictHomNumeratorTranspose` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictQuotientDiagonalNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.SupportedHomCocycleNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.TateTwistLocallyFree` | - | 1 | proof | 4 |
| `Sheaf.Paper.TraceBaseChangeFirst` | - | 3 | proof | 4 |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.CompletedCoefficientFreeResolution` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleOpenScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.PointRingedEvaluationModel` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.BalancedTensorChain` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.SliceTensorIntegerShiftCompatibility` | - | 3 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection` | - | 10 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportComparisonSectionModel` | - | 2 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerExchange` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedScalarUnitAdjunction` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletionMateComparison` | - | 21 | proof | 5 |
| `Sheaf.Paper.DerivedOpenSquareRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.DiagonalTowerSystem` | - | 1 | proof | 5 |
| `Sheaf.Paper.GeometricStalkPerfect` | - | 4 | proof | 5 |
| `Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization` | - | 1 | proof | 5 |
| `Sheaf.Paper.IdentityOpenUnderivedSquareNormalization` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralBoundedStratumBaseChange` | - | 2 | proof | 5 |
| `Sheaf.Paper.IntegralCompositionCounitImages` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralConstantModelHeart` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralHeartLocalModel` | - | 9 | proof | 5 |
| `Sheaf.Paper.IntegralLineReductionRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralTwistBaseChange` | - | 1 | proof | 5 |
| `Sheaf.Paper.IsomorphismScalarAugmentationCone` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.Paper.QuotientDiagramScalarProjection` | - | 1 | proof | 5 |
| `Sheaf.Paper.RamifiedPullbackTowerIdentification` | - | 1 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackComposition` | - | 1 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | - | 1 | proof | 5 |
| `Sheaf.Paper.SemilinearDerivedCalculus` | - | 1 | proof | 5 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | - | 1 | proof | 5 |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | - | 1 | proof | 5 |
| `Sheaf.Paper.StrictDvrReductionTriangles` | - | 1 | proof | 5 |
| `Sheaf.Paper.StrictQuotientScalarBalancing` | - | 1 | proof | 5 |
| `Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle` | - | 1 | proof | 5 |
| `Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle` | - | 1 | proof | 5 |
| `Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization` | - | 1 | proof | 5 |
| `Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | - | 6 | proof | 5 |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | - | 1 | proof | 5 |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | - | 2 | proof | 5 |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ClassicalSupportCounitIdentification` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor` | - | 4 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary` | - | 6 | proof | 6 |
| `Sheaf.Paper.ClassicalLocalizationTriangleTransport` | - | 1 | proof | 6 |
| `Sheaf.Paper.CommonLinePositiveScalarPowers` | - | 1 | proof | 6 |
| `Sheaf.Paper.ContinuousQbarConstructibleGenerators` | - | 1 | proof | 6 |
| `Sheaf.Paper.EllCoefficientFiber` | - | 3 | proof | 6 |
| `Sheaf.Paper.FiniteRingSectionDeformation` | - | 11 | proof | 6 |
| `Sheaf.Paper.IntegralResidueClassTriangleClosure` | - | 1 | proof | 6 |
| `Sheaf.Paper.NormalizedErrorTowerVanishing` | - | 1 | proof | 6 |
| `Sheaf.Paper.PowerTorsionSheafLimitComplete` | - | 2 | proof | 6 |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | - | 1 | proof | 6 |
| `Sheaf.Paper.PurSequenceAdjointResolutionShifts` | - | 1 | proof | 6 |
| `Sheaf.Paper.SemilinearKFlatTowerModel` | - | 1 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarPullbackSquare` | - | 1 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarTensorTower` | - | 7 | proof | 6 |
| `Sheaf.Paper.StratifiedConstantModelProductBound` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection` | - | 1 | proof | 6 |
| `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel` | - | 11 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting` | - | 1 | proof | 7 |
| `Sheaf.Compactification.NagataDensityNormalizationSheaves` | - | 1 | proof | 7 |
| `Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedCoefficientTensorNormalization` | - | 1 | proof | 7 |
| `Sheaf.Paper.FiniteOpenProductSwap` | - | 1 | proof | 7 |
| `Sheaf.Paper.FiniteProperProductTranspose` | - | 1 | proof | 7 |
| `Sheaf.Paper.FlatSingleScalarConventions` | - | 1 | proof | 7 |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | - | 4 | proof | 7 |
| `Sheaf.Paper.LocalModelTorBoundDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.TAdmissibleDualizableTruncations` | - | 1 | proof | 7 |
| `Sheaf.SixFunctors.OrdinaryProEtaleDirectImagePlusComparison` | - | 3 | proof | 7 |
| `Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology` | - | 7 | proof | 8 |
| `Sheaf.Paper.AdmissibleScalarRealizationExact` | - | 1 | proof | 8 |
| `Sheaf.Paper.ScalarPerfectDualRealization` | - | 10 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.NormalSchemeGaloisInertiaPresentation` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents` | - | 1 | proof | 9 |
| `Sheaf.Paper.AllContinuousScalarMate` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier` | - | 1 | proof | 10 |
| `Sheaf.CategoryTheory.SubterminalDerivedImageCalculus` | - | 1 | proof | 10 |
| `Sheaf.FieldTheory.InertiaRestrictionSurjective` | - | 1 | proof | 10 |
| `Sheaf.RingTheory.HenselianGlobalInertiaComparison` | - | 1 | proof | 10 |
| `Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover` | - | 1 | proof | 11 |
| `Sheaf.FieldTheory.GaloisPrimeResidueLifting` | - | 1 | proof | 11 |
| `Sheaf.RingTheory.IntegralComponentHenselianPermanence` | - | 1 | proof | 11 |
| `Sheaf.RingTheory.IntegralNormalResidueEtaleSplitting` | - | 1 | proof | 11 |
| `Sheaf.RingTheory.RegularLocalPicardZero` | - | 1 | proof | 11 |
| `Sheaf.RingTheory.StrictHenselizationFiniteLifts` | - | 1 | proof | 11 |
| `Sheaf.TraceFormula.HenselizationPrimeIndEtale` | - | 1 | proof | 11 |
| `Sheaf.TraceFormula.NagataInvertPrime` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.AffineNonZeroDivisorComplementDense` | - | 1 | proof | 12 |
| `Sheaf.FieldTheory.NormalFiniteAutSeparableSubfield` | - | 1 | proof | 12 |
| `Sheaf.RingTheory.IntegralFiniteResidueModel` | - | 1 | proof | 12 |
| `Sheaf.RingTheory.K0ClassTrivialInvertible` | - | 1 | proof | 12 |
| `Sheaf.RingTheory.LocalizedFiniteModuleSpread` | - | 1 | proof | 12 |
| `Sheaf.TraceFormula.InvertibleModuleK0Class` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor` | - | 1 | proof | 13 |
| `Sheaf.RingTheory.K0DeterminantMap` | - | 1 | proof | 13 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 14 |
| `Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence` | - | 7 | proof | 14 |
| `Sheaf.RingTheory.FiniteProjectiveOfStandardCover` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 16 |
| `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` | - | 5 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 18 |

## Stage 3: waiting for statements of dependencies (28)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | `lem-zl-constant-geometric-stalk-unit` |
| `Sheaf.Algebra.Homology.PerfectTensorRoosCompletion` | - | 15 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | - | 2 | `lem-sf-locally-closed-relative-transpose-normalization` |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | - | 4 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | - | 1 | `lem-per-adic-normalized-fibre-comparisons` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-signed-line-derived-base-change` |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | `lem-coef-enriched-sequence-projection-formula` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | - | 1 | `lem-per-rational-realization-finite-cone-models` |
| `Sheaf.Paper.FiniteTypeCoordinateSupportOrientation` | - | 3 | `lem-pur-closed-finite-adjoint-counit-transport` |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | - | 1 | `lem-trf-point-transport-strict-quotient` |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | `lem-a1-finite-pullback-strict-tower-comparison` |
| `Sheaf.Paper.IntegralTensorPullback` | - | 8 | `lem-sfb-integral-pullback-strict-roos-normalization` |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | - | 1 | `lem-fd-local-frobenius-coefficient-extension` |
| `Sheaf.Paper.NormalContinuousAlgClMonodromy` | - | 1 | `lem-sfb-normal-generic-continuous-sections` |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | - | 4 | `lem-weil-point-derived-sections-tensor-descent` |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | `lem-sf-tensor-comparison-localization-descent` |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | `lem-weil-point-derived-sections-tensor-descent` |
| `Sheaf.Paper.PurityConventions` | - | 11 | `sk-def-sf-operations` |
| `Sheaf.Paper.PurityGeneralAdmissibility` | - | 1 | `lem-pur-affine-chart-exceptional-identification` |
| `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` | - | 1 | `lem-sfb-integral-ambient-tower-comparison` |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | - | 1 | `lem-fd-whole-tower-integral-pullback-comparison` |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | `lem-sf-cbc-localized-strict-tensor-descent` |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | - | 4 | `lem-sp-cofinal-finite-reduction-constructibility` |
| `Sheaf.Paper.TameBoundaryScalarComparison` | - | 1 | `lem-sfb-transverse-tame-open-shriek-exchange` |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | - | 1 | `lem-sfb-continuous-algcl-open-finiteness` |

## Stage 3: held for an open upstream PR (16)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
