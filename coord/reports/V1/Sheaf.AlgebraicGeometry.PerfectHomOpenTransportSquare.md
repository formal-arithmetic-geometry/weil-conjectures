## What changed

Proved `AlgebraicGeometry.perfect_hom_open_transport_square` in
`Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare`, with its statement and visibility
unchanged. The proof follows the original cartesian-square/coherence argument. The module uses `import all Sheaf.AlgebraicGeometry.PerfectHomTransport` to reuse
its existing private `cc_assoc`, `tr`, `trTo`, `trTo_assoc`, `trTo_congr`, and
`homMap_trTo` directly. The only additional calculations are the proved private
`tr_comp_source`, `trTo_comp_source`, and `homMap_natural`. Naturality handles the
restriction comparison σ without any further property of its adjunction construction.
No existing transport theorem is copied, and no other module's interface changes.
Replaced the unused public import `Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone` by its
actual statement dependency `Sheaf.AlgebraicGeometry.PerfectHomTransport`. Retained
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData`. Added change record
`coord/changes/perfect-hom-open-transport-square-imports.md` for public-import pruning
and the private helper section commands. Updated the existing node's
proof and proof_origin; its proof dependencies are unchanged. No definitions, existing
signatures, other modules, or target statements were changed.

The selected composition and derived-pullback definitions are locally irreducible during
the calculations. Elaboration respects transparency in the helpers and the theorem proof;
the existing statement is elaborated under its original option. Profiling identified
expensive reduction of the selected derived-functor data. These local options avoid it
without modifying any shared definition or increasing the compiler's time limit.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.perfect_hom_open_transport_square`
(node `lem-pc-perfect-hom-open-transport-square`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The proof uses
`AlgebraicGeometry.exists_derivedPullbackComposition` and the existing derived-pullback
and restriction data. The independent axiom check finds only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

The unit record `sk-thm-picard-semicon` has empty realized statement/step lists;
no unit statement or realized proof step was bypassed. Identity arrows, empty opens,
and zero objects require no additional hypotheses: the proof uses only functor laws,
isomorphism cancellation and the pullback universal property.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone`, node
`lem-pc-perfect-hom-push-pull-cocone`. A representing cocone is unnecessary for this
coherence identity. No original proof_deps node was removed: all three are used.

The complete source-import closure difference for this item contains 545 project
modules, listed below with every matching DAG node. This is item-local pruning, not a
claim that those modules are absent from every target's closure. The maintainer's ledger
and queue determine which can be pruned globally. A dash means no node's primary Lean
module record matches that source module.

| Module no longer reached through this item | Matching DAG nodes |
|---|---|
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat` | `lem-pc-sites-modules-j-shriek-flat` |
| `Sheaf.Algebra.Homology.BaseDerivedExtensionLinear` | `lem-pc-base-derived-extension-linear` |
| `Sheaf.Algebra.Homology.BaseDerivedExtensionResolution` | `lem-pc-base-derived-extension-resolution` |
| `Sheaf.Algebra.Homology.BaseDerivedExtensionScalar` | `lem-pc-base-derived-extension-scalar` |
| `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyAction` | `lem-pc-base-derived-tensor-cohomology-action` |
| `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` | `def-pc-base-derived-tensor-cohomology-model` |
| `Sheaf.Algebra.Homology.BaseDerivedTensorCounitLinear` | `lem-pc-base-derived-tensor-counit-linear` |
| `Sheaf.Algebra.Homology.BaseTensorOrdinaryDegreeIso` | `lem-pc-base-tensor-ordinary-degree-iso` |
| `Sheaf.Algebra.Homology.BaseTensorOrdinaryIso` | `lem-pc-base-tensor-ordinary-iso` |
| `Sheaf.Algebra.Homology.CoproductKProjective` | `lem-pc-coproduct-kprojective` |
| `Sheaf.Algebra.Homology.FilteredFreeKProjective` | `lem-pc-filtered-free-kprojective`, `lem-pc-filtered-free-kprojective-stage`, `lem-pc-filtered-free-kprojective-telescope` |
| `Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly` | `lem-pc-filtered-free-kprojective-assembly` |
| `Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep` | `lem-pc-filtered-free-kprojective-step` |
| `Sheaf.Algebra.Homology.FilteredFreeResolution` | `lem-pc-derived-filtered-free-resolution` |
| `Sheaf.Algebra.Homology.FilteredFreeTelescopeSplitting` | `lem-pc-filtered-free-telescope-splitting` |
| `Sheaf.Algebra.Homology.FreeComplexCover` | `lem-pc-derived-free-complex-cover` |
| `Sheaf.Algebra.Homology.FreeCoverBicomplex` | `lem-pc-derived-free-cover-bicomplex` |
| `Sheaf.Algebra.Homology.FreeCoverColumns` | `lem-pc-derived-free-cover-columns` |
| `Sheaf.Algebra.Homology.KFlatTensorProduct` | `lem-pc-kflat-tensor-product` |
| `Sheaf.Algebra.Homology.KInjectiveProducts` | `lem-pc-ringed-space-product-kinjective` |
| `Sheaf.Algebra.Homology.KernelShiftedMappingCone` | `lem-weil-degreewise-epi-kernel-cocone-qis` |
| `Sheaf.Algebra.Homology.LargeFilteredFreeResolution` | `lem-pc-large-filtered-free-resolution` |
| `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` | `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` |
| `Sheaf.Algebra.Homology.LowerTruncationStepTriangle` | `lem-pc-derived-lower-truncation-step-triangle` |
| `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkOutside` | `lem-sc-module-extension-by-zero-stalk-maps-outside` |
| `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitEpi` | `lem-sc-module-extension-by-zero-unit-epi` |
| `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitFaithful` | `lem-sc-module-extension-by-zero-unit-mono-faithful-aux` |
| `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitIsIso` | `lem-sc-module-extension-by-zero-unit-isiso` |
| `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitMono` | `lem-sc-module-extension-by-zero-unit-mono` |
| `Sheaf.Algebra.Homology.RoosComparisonHomotopies` | `lem-weil-roos-comparison-homotopies` |
| `Sheaf.Algebra.Homology.RoosComparisonHomotopyRetract` | `lem-weil-roos-comparison-homotopy-retract` |
| `Sheaf.Algebra.Homology.RoosComparisonMaps` | `lem-weil-roos-comparison-maps` |
| `Sheaf.Algebra.Homology.RoosComplex` | `lem-weil-derived-limit-roos-complex` |
| `Sheaf.Algebra.Homology.RoosSplitComparison` | `lem-weil-roos-split-comparison` |
| `Sheaf.Algebra.Homology.TensorActionOfAdditiveFunctor` | `lem-pc-tensor-action-additive-functor` |
| `Sheaf.Algebra.Homology.TotalFreeFiltration` | `lem-pc-derived-total-free-filtration` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelEven` | `lem-pc-derived-total-filtration-cokernel-even` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOdd` | `lem-pc-derived-total-filtration-cokernel-odd` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOddAux` | `lem-pc-derived-total-filtration-cokernel-odd-core` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective` | `lem-pc-derived-total-filtration-even-quotient-bijective`, `lem-pc-derived-total-filtration-even-quotient-injective`, `lem-pc-derived-total-filtration-even-quotient-surjective` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap` | `lem-pc-derived-total-filtration-even-quotient-map` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationExhaustive` | `lem-pc-derived-total-filtration-exhaustive` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective` | `lem-pc-derived-total-filtration-odd-quotient-bijective` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientMap` | `lem-pc-derived-total-filtration-odd-quotient-map` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationQuotients` | `lem-pc-derived-total-filtration-quotients` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationStepRetraction` | `lem-pc-derived-total-filtration-step-retraction` |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationTerms` | `lem-pc-derived-total-filtration-stable` |
| `Sheaf.Algebra.Homology.TowerEvaluationKInjective` | `lem-weil-tower-evaluation-kinjective` |
| `Sheaf.Algebra.Homology.TowerSplitComplexReplacement` | `lem-weil-tower-split-complex-replacement` |
| `Sheaf.Algebra.Homology.ZeroDifferentialFreeCoproduct` | `lem-pc-zero-differential-free-coproduct` |
| `Sheaf.AlgebraicGeometry.AffineCapSectionOpen` | `lem-sc-affine-cap-section-open` |
| `Sheaf.AlgebraicGeometry.AffineCapSectionOpenAlgebra` | `lem-sc-affine-cap-section-open-algebra` |
| `Sheaf.AlgebraicGeometry.AffineCapSectionOpenDictionary` | `lem-sc-affine-cap-section-open-dictionary` |
| `Sheaf.AlgebraicGeometry.AffineChartTotalTensor` | `lem-pc-affine-chart-total-tensor` |
| `Sheaf.AlgebraicGeometry.AffineDerivedCounitHomologyFactorization` | `new-affine-derived-counit-homology-factorization` |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel` | `lem-pc-affine-derived-pullback-module-model` |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | `lem-pc-affine-derived-pullback-tensor-tilde` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison` | `lem-pc-affine-derived-sections-homology-comparison` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom` | `new-affine-derived-sections-truncated-bottom` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncationIso` | `new-affine-derived-sections-truncation-iso` |
| `Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison` | `lem-pc-affine-derived-tensor-chart-comparison` |
| `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison` | `new-affine-derived-tilde-homology-comparison` |
| `Sheaf.AlgebraicGeometry.AffineDerivedUnitHomologyIsIso` | `new-affine-derived-unit-homology-isIso` |
| `Sheaf.AlgebraicGeometry.AffineDerivedUnitIsomorphism` | `lem-pc-affine-derived-unit-isomorphism` |
| `Sheaf.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing` | `lem-pc-affine-higher-direct-image-cohomology-vanishing` |
| `Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison` | `lem-pc-affine-kflat-pullback-chart-comparison` |
| `Sheaf.AlgebraicGeometry.AffineLocalizationSheafification` | `lem-pc-affine-localization-sheafification` |
| `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf` | `lem-pc-affine-localizing-presheaf-basis-sheaf` |
| `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification` | `lem-pc-affine-localizing-presheaf-sheafification` |
| `Sheaf.AlgebraicGeometry.AffineModuleComplexRepresentative` | `lem-pc-affine-module-complex-representative` |
| `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalization` | `lem-sc-invert-s-cohomology-affine-open` |
| `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalizationZero` | `lem-sc-invert-s-cohomology-affine-open-zero` |
| `Sheaf.AlgebraicGeometry.AffineOpenHigherDirectImageSectionsIso` | `lem-pc-affine-open-higher-direct-image-sections-iso` |
| `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing` | `pqf-lem-affine-vanishing` |
| `Sheaf.AlgebraicGeometry.AffineOpenSectionFractionLocalization` | `lem-sc-affine-open-section-fraction-localization` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionConstruction` | `new-affine-qcoh-derived-adjunction-construction` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionUnitCounit` | `new-affine-qcoh-derived-adjunction-unit-counit` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` | `lem-pc-affine-qcoh-derived-equivalence` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` | `new-affine-qcoh-derived-equivalence-core` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift` | `new-affine-qcoh-derived-equivalence-shift` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated` | `new-affine-qcoh-derived-tilde-triangulated` |
| `Sheaf.AlgebraicGeometry.AffineSectionLocalization` | `lem-sc-affine-section-localization` |
| `Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso` | `new-affine-tilde-derived-sections-unit-isIso` |
| `Sheaf.AlgebraicGeometry.AffineTildeTotalTensor` | `lem-pc-affine-tilde-total-tensor` |
| `Sheaf.AlgebraicGeometry.Ample` | `def-weil-pbc-ample-invertible-module` |
| `Sheaf.AlgebraicGeometry.Coherent` | `pqf-def-coherent` |
| `Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero` | `lem-sc-cohomology-fraction-eventually-zero` |
| `Sheaf.AlgebraicGeometry.CohomologyFractionPresentation` | `def-sc-cohomology-fraction-presentation` |
| `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing` | `lem-sc-invert-s-cohomology-gluing` |
| `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux` | `lem-sc-invert-s-cohomology-gluing-aux` |
| `Sheaf.AlgebraicGeometry.DerivedAdjoint` | `lem-pc-ringed-spaces-derived-adjoint` |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison` | `lem-pc-derived-direct-image-affine-truncation-comparison` |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh` | `lem-pc-derived-direct-image-bounded-below-qcoh` |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` | `lem-pc-restrict-derived-direct-image-open` |
| `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh` | `lem-pc-derived-direct-image-preserves-qcoh` |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound` | `lem-pc-derived-direct-image-uniform-truncation-bound` |
| `Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization` | `lem-pc-derived-functor-truncation-stabilization` |
| `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh` | `lem-pc-derived-open-restriction-qcoh-iff` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | `lem-pc-derived-pullback-kflat-tensor-model` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` | `lem-pc-derived-pullback-open-restriction-universes` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackPreservesQCoh` | `lem-pc-derived-pullback-qcoh-component` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` | `lem-pc-derived-pullback-tensor-comparison-descent` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct` | `lem-pc-derived-pullback-tensor-product` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh` | `lem-pc-derived-pullback-tensor-qcoh` |
| `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses` | `lem-pc-derived-tensor-open-restriction-universes` |
| `Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh` | `lem-pc-derived-tensor-qcoh-component` |
| `Sheaf.AlgebraicGeometry.DerivedTensorStructure` | `def-pc-scheme-derived-tensor-structure` |
| `Sheaf.AlgebraicGeometry.DirectImageHomologyAffineDetection` | `lem-pc-direct-image-homology-affine-detection` |
| `Sheaf.AlgebraicGeometry.DirectImageTruncationTailBound` | `lem-pc-direct-image-truncation-tail-bound` |
| `Sheaf.AlgebraicGeometry.FiniteRetractSheavesAffineTrivialization` | `lem-pc-finite-retract-sheaves-affine-trivialization` |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` | `def-weil-pbc-flat-base-change-open-choices` |
| `Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing` | `lem-pc-higher-direct-image-affine-basis-vanishing` |
| `Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction` | `lem-pc-higher-direct-image-open-restriction` |
| `Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators` | `lem-pc-higher-direct-image-section-denominators` |
| `Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion` | `lem-pc-higher-direct-image-section-torsion` |
| `Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization` | `lem-pc-higher-image-cohomology-presheaf-localization` |
| `Sheaf.AlgebraicGeometry.InvertSCOhomology` | `lem-sc-invert-s-cohomology` |
| `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization` | `lem-sc-p1-invertible-section-localization` |
| `Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent` | `lem-pc-kflat-bifunctor-iso-descent` |
| `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison` | `lem-pc-kflat-derived-tensor-comparison` |
| `Sheaf.AlgebraicGeometry.LerayComplexCocycleComparison` | `lem-pc-leray-complex-cocycle-comparison` |
| `Sheaf.AlgebraicGeometry.LerayDegenerateSections` | `lem-pc-leray-degenerate-sections` |
| `Sheaf.AlgebraicGeometry.LerayEdgeCocycleData` | `lem-pc-leray-edge-cocycle-data` |
| `Sheaf.AlgebraicGeometry.LerayEdgeGrothendieckComparison` | `lem-pc-leray-edge-grothendieck-comparison` |
| `Sheaf.AlgebraicGeometry.LerayEdgeVanishingIso` | `lem-pc-leray-edge-vanishing-iso` |
| `Sheaf.AlgebraicGeometry.LeraySectionsResolutionComparison` | `lem-pc-leray-sections-resolution-comparison` |
| `Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound` | `lem-pc-local-uniform-higher-direct-image-bound` |
| `Sheaf.AlgebraicGeometry.LocalizingPrincipalCoverGluing` | `lem-pc-localizing-principal-cover-gluing` |
| `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty` | `lem-weil-pbc-ml-sets-tower-limit-nonempty` |
| `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology` | — |
| `Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion` | `lem-weil-pbc-module-cech-vanishing-criterion` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` | `def-weil-pbc-module-cohomology-fmap` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison` | `lem-sc-module-cohomology-source-comparison` |
| `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic` | `lem-weil-pbc-module-injective-open-cover-cech-acyclic` |
| `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives` | `lem-weil-pbc-module-open-restriction-injectives` |
| `Sheaf.AlgebraicGeometry.ModulePullbackTensor` | `lem-weil-pbc-module-pullback-tensor` |
| `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic` | `lem-weil-pbc-module-pushforward-injective-acyclic` |
| `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveCechVanishing` | `lem-weil-pbc-module-pushforward-injective-cech-vanishing` |
| `Sheaf.AlgebraicGeometry.ModuleSectionsAcyclicOfCohomologyVanishing` | `lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing` |
| `Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1` | `lem-weil-pbc-module-ses-cech-h1-surjective` |
| `Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity` | `lem-pc-affine-extension-section-surjectivity` |
| `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor` | `lem-weil-pbc-affine-tilde-tensor` |
| `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk` | `lem-weil-pbc-affine-tilde-tensor-stalk-bijective` |
| `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction` | `lem-weil-pbc-module-extension-by-zero-adjunction` |
| `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula` | `lem-weil-pbc-module-extension-by-zero-hom-formula` |
| `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroInside` | `new-extension-by-zero-inside-stalk` |
| `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroOutside` | `new-extension-by-zero-outside-stalk` |
| `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroUnitStalks` | `lem-weil-pbc-module-extension-by-zero-unit-stalks` |
| `Sheaf.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport` | `lem-pc-inverse-image-stalk-scalar-transport` |
| `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction` | `lem-pc-kflat-open-restriction` |
| `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde` | `lem-pc-affine-tilde-kflat` |
| `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` | `lem-weil-pbc-quasi-coherent-module-cokernel-image` |
| `Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension` | `lem-pc-quasi-coherent-extension` |
| `Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso` | `lem-pc-open-restriction-stalk-extension-iso` |
| `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison` | `lem-weil-pbc-module-restriction-tensor-comparison` |
| `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` | `lem-weil-pbc-module-stalk-pullback` |
| `Sheaf.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso` | `lem-weil-pbc-module-pullback-tensor-iso-criterion` |
| `Sheaf.AlgebraicGeometry.Modules.TildeStalkTensorComparison` | `lem-pc-affine-tilde-stalk-tensor-comparison` |
| `Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` | `lem-sc-nonvanishing-iff-generates-at` |
| `Sheaf.AlgebraicGeometry.NonvanishingLocusRestrict` | `lem-sc-nonvanishing-locus-restrict` |
| `Sheaf.AlgebraicGeometry.OpenCohomologyFractionZeroComparison` | `lem-sc-open-cohomology-fraction-zero-comparison` |
| `Sheaf.AlgebraicGeometry.OpenCohomologyZeroRestriction` | `lem-sc-open-cohomology-zero-restriction` |
| `Sheaf.AlgebraicGeometry.OpenCohomologyZeroSections` | `lem-sc-open-cohomology-zero-sections` |
| `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison` | `lem-pqf-open-module-cohomology-comparison` |
| `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel` | `lem-pc-open-restriction-kflat-model` |
| `Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality` | `lem-pc-open-restriction-tensor-natural` |
| `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor` | `lem-pc-open-restriction-total-tensor` |
| `Sheaf.AlgebraicGeometry.OpenSectionFractionPresentation` | `def-sc-open-section-fraction-presentation` |
| `Sheaf.AlgebraicGeometry.PerfectComplex` | `def-pc-perfect-complex` |
| `Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone` | `lem-pc-perfect-hom-push-pull-cocone` |
| `Sheaf.AlgebraicGeometry.PerfectHomStageColimit` | `lem-pc-perfect-hom-stage-colimit` |
| `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh` | `lem-sc-perfect-qcoherent` |
| `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` | `def-pur-pseudo-coherent-complex` |
| `Sheaf.AlgebraicGeometry.PseudoCoherentQCoh` | `lem-sc-pseudo-coherent-qcoh` |
| `Sheaf.AlgebraicGeometry.PseudoCoherentQCohDegree` | `lem-sc-pseudo-coherent-qcoh-degree` |
| `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso` | `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso` |
| `Sheaf.AlgebraicGeometry.QCohTruncationDerivedLimit` | `lem-pc-qcoh-truncation-derived-limit` |
| `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction` | `lem-sc-invert-s-cohomology-induction` |
| `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty` | `property-intersection-qc-affine` |
| `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion` | `pqf-lem-qcoh-compact-section-power-torsion` |
| `Sheaf.AlgebraicGeometry.ResolutionOpenComparisonMap` | `def-pc-resolution-open-comparison-map` |
| `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionCore` | `lem-pc-resolution-open-restriction-core` |
| `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionNatural` | `lem-pc-resolution-open-restriction-natural` |
| `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison` | `lem-pc-resolution-open-scalar-comparison` |
| `Sheaf.AlgebraicGeometry.ResolutionOpenScalarCore` | `lem-pc-resolution-open-scalar-core` |
| `Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar` | `lem-pc-resolution-sections-homology-scalar` |
| `Sheaf.AlgebraicGeometry.ResolutionUnitTwistComparison` | `lem-pc-resolution-unit-twist-comparison` |
| `Sheaf.AlgebraicGeometry.RestrictedResolutionSectionsExist` | `lem-pc-restricted-resolution-sections-exist` |
| `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology` | `lem-pc-ringed-space-sheafification-cohomology` |
| `Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso` | `lem-pc-scheme-module-free-yoneda-iso` |
| `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives` | `lem-weil-pbc-scheme-modules-enough-injectives` |
| `Sheaf.AlgebraicGeometry.SectionClearingDenominatorsQCQS` | `lem-sc-p1-section-clearing-denominators-qcqs` |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalDenominators` | `lem-pc-section-cohomology-principal-denominators` |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` | `lem-pc-section-cohomology-principal-localization` |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalTorsion` | `lem-pc-section-cohomology-principal-torsion` |
| `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons` | `lem-pc-section-cohomology-unit-comparisons` |
| `Sheaf.AlgebraicGeometry.SectionCohomologyUntwistedComparisons` | `lem-pc-section-cohomology-untwisted-comparisons` |
| `Sheaf.AlgebraicGeometry.SectionFractionPresentation` | `def-sc-section-fraction-presentation` |
| `Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap` | `lem-sc-p1-section-fraction-restriction-map` |
| `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus` | `lem-weil-pbc-section-nonvanishing-zero-locus` |
| `Sheaf.AlgebraicGeometry.SectionRestrictionSTorsion` | `lem-sc-p1-section-restriction-s-torsion` |
| `Sheaf.AlgebraicGeometry.SeparatedOpenInduction` | `lem-sc-invert-s-cohomology-separated-induction` |
| `Sheaf.AlgebraicGeometry.SingleFiniteRetractSheafAffineTrivialization` | `new-pc-single-retract-sheaf-affine-trivialization` |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement` | `lem-pc-strictly-perfect-finite-free-refinement` |
| `Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition` | `lem-sc-tensor-power-open-restriction-addition` |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` | `lem-sc-tensor-power-section-open-restriction` |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN` | `def-sc-tensor-power-open-restriction-comparisons`, `lem-sc-tensor-power-section-open-restriction-N` |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT` | `lem-sc-tensor-power-section-open-restriction-T` |
| `Sheaf.AlgebraicGeometry.TensorPullbackTilde` | `lem-weil-pbc-tilde-pullback-base-change` |
| `Sheaf.AlgebraicGeometry.TensorUnitPowerScalar` | `lem-pc-tensor-unit-power-scalar` |
| `Sheaf.AlgebraicGeometry.TruncationDerivedLimit` | `lem-pc-ringed-space-truncation-derived-limit` |
| `Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound` | `lem-pc-unbounded-derived-functor-cohomological-bound` |
| `Sheaf.AlgebraicGeometry.UniformDirectImageBoundCore` | `lem-pc-uniform-direct-image-bound-core` |
| `Sheaf.AlgebraicGeometry.UniformInverseAffineSectionsBound` | `lem-pc-uniform-inverse-affine-sections-bound` |
| `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution` | `lem-weil-pbc-set-cech-nerve-free-resolution` |
| `Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` | `lem-sc-ext-epi-effacement` |
| `Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom` | `lem-sc-ext-right-derived-hom` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization` | `lem-weil-pbc-horseshoe-defect-factorization` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap` | `lem-weil-pbc-horseshoe-degreewise-map` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor` | `lem-weil-pbc-horseshoe-delta-functor` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection` | `lem-weil-pbc-horseshoe-homotopy-correction` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift` | `lem-weil-pbc-horseshoe-correction`, `lem-weil-pbc-horseshoe-morphism-lift`, `lem-weil-pbc-horseshoe-preliminary-data` |
| `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions` | `lem-sp-horseshoe-prescribed-resolutions` |
| `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows` | `lem-sp-horseshoe-prescribed-row-construction` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions` | `lem-weil-pbc-injective-resolution-ses` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural` | `lem-sc-acyclic-comparison-natural` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` | `lem-weil-pbc-derived-functor-long-exact` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare` | `lem-sc-injectively-exact-square-resolution-short-exact` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryExact` | `lem-sc-injectively-exact-square-boundary-exact` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryNaturality` | `lem-sc-injectively-exact-square-boundary-naturality` |
| `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundarySquareNaturality` | `lem-sc-injectively-exact-square-boundary-square-naturality` |
| `Sheaf.CategoryTheory.AbutmentFinitePageComparison` | `lem-sp-abutment-finite-page-comparison` |
| `Sheaf.CategoryTheory.AbutmentImageFiltration` | `lem-sp-abutment-image-filtration` |
| `Sheaf.CategoryTheory.CanonicalResolutionCompositeUnitComparison` | `lem-pc-canonical-resolution-composite-unit-comparison` |
| `Sheaf.CategoryTheory.CanonicalResolutionDerivedIso` | `def-pc-canonical-resolution-derived-iso` |
| `Sheaf.CategoryTheory.CanonicalResolutionHomologyComparison` | `lem-pc-canonical-resolution-homology-comparison` |
| `Sheaf.CategoryTheory.DeltaFunctor` | `def-weil-pbc-delta-functor` |
| `Sheaf.CategoryTheory.DerivedCoupleBoundaryVanishes` | `lem-sp-derived-couple-boundary-vanishes` |
| `Sheaf.CategoryTheory.DerivedCoupleExact` | `lem-sp-derived-couple-exact`, `lem-sp-derived-couple-image-prefix` |
| `Sheaf.CategoryTheory.DerivedCoupleKernelIdentities` | `lem-sp-derived-couple-kernel-identities` |
| `Sheaf.CategoryTheory.DerivedCoupleMapConstruction` | `lem-sp-derived-map-construction` |
| `Sheaf.CategoryTheory.DerivedCoupleMapExactness` | `lem-sp-derived-map-exactness` |
| `Sheaf.CategoryTheory.DerivedCoupleMapUniqueness` | `lem-sp-derived-couple-map-uniqueness` |
| `Sheaf.CategoryTheory.DerivedLimitEventuallyIso` | `lem-pc-derived-limit-eventually-iso` |
| `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups` | `lem-pc-derived-limit-roos-abelian-groups`, `lem-pc-tower-enough-injectives` |
| `Sheaf.CategoryTheory.EffaceableDeltaFunctorSuccessor` | `lem-weil-pbc-effaceable-delta-functor-successor` |
| `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal` | `lem-weil-pbc-effaceable-delta-functor-universal` |
| `Sheaf.CategoryTheory.EffacingSequenceComparison` | `lem-weil-pbc-effacing-sequence-comparison` |
| `Sheaf.CategoryTheory.EffacingSequencePushout` | `lem-weil-pbc-effacing-sequence-pushout` |
| `Sheaf.CategoryTheory.ExactCouple` | `def-sp-exact-couple` |
| `Sheaf.CategoryTheory.ExactCoupleConvergence` | `def-sp-convergence` |
| `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` | `lem-sp-finite-cycle-derived-comparison` |
| `Sheaf.CategoryTheory.FiniteCycleKernelPresentation` | `lem-sp-finite-cycle-kernel-presentation` |
| `Sheaf.CategoryTheory.FinitePageGradedQuotient` | `lem-sp-finite-page-graded-quotient` |
| `Sheaf.CategoryTheory.FinitePageImageLift` | `lem-sp-finite-page-image-lift` |
| `Sheaf.CategoryTheory.FinitePageImageQuotient` | `lem-sp-finite-page-image-quotient` |
| `Sheaf.CategoryTheory.GrothendieckCocycleComparison` | `lem-pc-grothendieck-cocycle-comparison` |
| `Sheaf.CategoryTheory.GrothendieckComposablePair` | `def-sp-composite-acyclicity` |
| `Sheaf.CategoryTheory.GrothendieckEdgeCocycle` | `lem-pc-grothendieck-edge-cocycle` |
| `Sheaf.CategoryTheory.GrothendieckHypercohomologyEdge` | `lem-pc-grothendieck-hypercohomology-edge` |
| `Sheaf.CategoryTheory.GrothendieckResolutionUnitComparison` | `lem-pc-grothendieck-resolution-unit-comparison` |
| `Sheaf.CategoryTheory.HalfPlaneConvergence` | `thm-sp-half-plane-convergence` |
| `Sheaf.CategoryTheory.HalfPlaneDiagonalColimits` | `lem-sp-half-plane-diagonal-colimits` |
| `Sheaf.CategoryTheory.HalfPlaneSharpBounds` | `lem-sp-half-plane-sharp-bounds` |
| `Sheaf.CategoryTheory.HalfPlaneWeakConvergence` | `lem-sp-half-plane-weak-convergence` |
| `Sheaf.CategoryTheory.HypercohomologyEdgeCocycle` | `lem-pc-hypercohomology-edge-cocycle` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdge` | `def-pc-hypercohomology-left-edge` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdgeCanonical` | `lem-pc-hypercohomology-edge-cocycle-canonical` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdgeNaturality` | `lem-pc-hypercohomology-left-edge-naturality` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdgeSingle` | `lem-pc-hypercohomology-left-edge-single` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdgeSingleAux` | `lem-pc-hypercohomology-left-edge-single-aux` |
| `Sheaf.CategoryTheory.HypercohomologyLeftEdgeTruncation` | `lem-pc-hypercohomology-left-edge-truncation` |
| `Sheaf.CategoryTheory.ImageFiltration` | `def-sp-image-filtration` |
| `Sheaf.CategoryTheory.InjectiveModulePresheaf` | `lem-weil-pbc-ringed-site-injective-module-injective-presheaf` |
| `Sheaf.CategoryTheory.InjectiveSplitTower` | `lem-pc-injective-split-tower-injective` |
| `Sheaf.CategoryTheory.InjectiveSplitTowerExtension` | `lem-pc-injective-split-tower-extension` |
| `Sheaf.CategoryTheory.InjectiveTowerEmbedding` | `lem-pc-tower-injective-embedding` |
| `Sheaf.CategoryTheory.KInjectiveBridge` | `def-sp-kinjective-bridge` |
| `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism` | `def-weil-tower-transition-endomorphism` |
| `Sheaf.CategoryTheory.MappedSingleCyclesShiftComparison` | `lem-pc-mapped-single-cycles-shift-comparison` |
| `Sheaf.CategoryTheory.MappedSingleInverseShift` | `lem-pc-mapped-single-inverse-shift` |
| `Sheaf.CategoryTheory.MittagLefflerLimitExact` | `lem-weil-pbc-mittag-leffler-limit-exact` |
| `Sheaf.CategoryTheory.NormalizedGradedFiniteKernel` | `lem-sp-normalized-graded-finite-kernel` |
| `Sheaf.CategoryTheory.RightDerivedCanonicalSingleUnit` | `lem-pc-right-derived-canonical-single-unit` |
| `Sheaf.CategoryTheory.RightDerivedCanonicalSingleUnitShift` | `lem-pc-right-derived-canonical-single-unit-shift` |
| `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso` | `lem-weil-pbc-derived-functor-truncation-iso`, `lem-weil-pbc-derived-functor-truncation-iso-epi`, `lem-weil-pbc-derived-functor-truncation-iso-mono` |
| `Sheaf.CategoryTheory.RightDerivedSingleDegreeComparison` | `def-pc-right-derived-single-degree-comparison` |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` | `lem-sbc-right-derived-single-unit-homology-comparison` |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | `lem-pc-right-derived-single-unit-shift-transport` |
| `Sheaf.CategoryTheory.RightDerivedUnitSingleDegree` | `lem-pc-right-derived-unit-single-degree` |
| `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` | `lem-weil-pbc-right-derived-universal-delta-functor` |
| `Sheaf.CategoryTheory.RoosAcyclicResolution` | `lem-pc-roos-functorial-acyclic-resolution` |
| `Sheaf.CategoryTheory.RoosFinitePrefixLimits` | `lem-pc-roos-finite-prefix-limits` |
| `Sheaf.CategoryTheory.RoosFinitePrefixes` | `lem-pc-roos-finite-prefix-construction` |
| `Sheaf.CategoryTheory.RoosPrefixAcyclic` | `lem-pc-roos-prefix-acyclic` |
| `Sheaf.CategoryTheory.SingleHomologyShiftComparison` | `lem-pc-single-homology-shift-comparison` |
| `Sheaf.CategoryTheory.SingleQuotientInverseShift` | `lem-pc-single-quotient-inverse-shift` |
| `Sheaf.CategoryTheory.SiteCechComplex` | `def-weil-pbc-site-cech-complex` |
| `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation` | `new-sheaf-cohomology-derived-evaluation` |
| `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections` | `lem-sc-site-cohomology-right-derived-sections` |
| `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` | `lem-sc-injective-module-abelian-acyclic-zariski` |
| `Sheaf.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic` | `lem-sc-injective-presheaf-module-nerve-acyclic` |
| `Sheaf.CategoryTheory.Sites.PresheafCechComplex` | `def-sc-presheaf-cech-complex` |
| `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective` | `lem-sc-presheaf-cech-ext-edge-injective` |
| `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeKernel` | `lem-sc-presheaf-cech-ext-edge-kernel` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafAugmentationExact` | `lem-sc-presheaf-cech-sheaf-augmentation-exact` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafHomComparison` | `lem-sc-presheaf-cech-sheaf-hom-comparison` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafPositiveExact` | `lem-sc-presheaf-cech-sheaf-positive-exact` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafResolution` | `lem-sc-presheaf-cech-sheaf-resolution` |
| `Sheaf.CategoryTheory.Sites.PresheafCechVanishingCriterion` | `lem-sc-presheaf-cech-vanishing-criterion` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` | `lem-sc-presheaf-free-ext-local-killing`, `lem-sc-presheaf-free-ext-local-killing-witness` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeNerveComparison` | `lem-sc-presheaf-free-nerve-comparison` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeNerveExact` | `lem-sc-presheaf-free-nerve-exact`, `lem-sc-presheaf-free-nerve-exact-eval`, `lem-sc-presheaf-free-nerve-exact-eval-glue` |
| `Sheaf.CategoryTheory.SubobjectHomologyStep` | `lem-sp-subobject-homology-step` |
| `Sheaf.CategoryTheory.SupportedComplexSingleRealization` | `lem-pc-supported-complex-single-realization` |
| `Sheaf.CategoryTheory.TowerSplitEnvelope` | `lem-weil-tower-split-envelope` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsCore` | `lem-weil-derived-countable-products-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsExistence` | `lem-weil-derived-countable-products-existence` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsProperties` | `lem-weil-derived-countable-products-properties` |
| `Sheaf.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit` | `lem-pc-derived-functor-commutes-derived-limit` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimit` | `def-weil-derived-limit` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence` | `lem-weil-derived-limit-existence` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts` | `lem-weil-derived-limit-products-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTower` | `lem-weil-derived-limit-tower-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone` | `lem-weil-derived-limit-tower-core-cone` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerProperty` | `lem-weil-derived-limit-tower-core-property` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle` | `lem-weil-derived-limit-tower-roos-triangle` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle` | `lem-weil-derived-limit-tower-core-property-triangle` |
| `Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization` | `lem-pc-milnor-boundary-factorization` |
| `Sheaf.CategoryTheory.Triangulated.MilnorProjectionFactorization` | `lem-pc-milnor-projection-factorization` |
| `Sheaf.CategoryTheory.Triangulated.MilnorSequence` | `lem-pc-derived-limit-milnor-sequence` |
| `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts` | `lem-pc-right-derived-functor-countable-products` |
| `Sheaf.CategoryTheory.Triangulated.RingedSpaceDerivedProducts` | `lem-pc-ringed-space-derived-products` |
| `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension` | `lem-weil-pbc-triangle-morphism-extension` |
| `Sheaf.CategoryTheory.TruncationAbutmentCocone` | `lem-sp-truncation-abutment-cocone` |
| `Sheaf.CategoryTheory.TruncationAbutmentCoconeAux` | `lem-sp-truncation-abutment-cocone-aux` |
| `Sheaf.CategoryTheory.TruncationCanonicalAbutment` | `lem-sp-truncation-canonical-abutment` |
| `Sheaf.CategoryTheory.TruncationCouple` | `def-sp-truncation-couple` |
| `Sheaf.CategoryTheory.TruncationHypercohomology` | `thm-sp-truncation-e2` |
| `Sheaf.CategoryTheory.TruncationQuadrantVanishing` | `lem-sp-truncation-quadrant-vanishing` |
| `Sheaf.CategoryTheory.TruncationRawExact` | `lem-sp-truncation-raw-exact` |
| `Sheaf.CategoryTheory.TruncationTriangle` | `lem-weil-pbc-truncation-triangle` |
| `Sheaf.Paper.CohomologyFractionComparison` | `lem-sc-cohomology-fraction-comparison` |
| `Sheaf.Paper.CohomologyFractionMayerVietorisExact` | `lem-sc-cohomology-fraction-mayer-vietoris-exact` |
| `Sheaf.Paper.CohomologyFractionMayerVietorisSquares` | `lem-sc-cohomology-fraction-mayer-vietoris-squares` |
| `Sheaf.Paper.CohomologySectionDivision` | `lem-sc-cohomology-section-division` |
| `Sheaf.Paper.DerivedTotalResolutionColumnZero` | `lem-pc-derived-total-resolution-column-zero` |
| `Sheaf.Paper.DerivedTotalResolutionHomologyInjective` | `lem-pc-derived-total-resolution-homology-injective` |
| `Sheaf.Paper.DerivedTotalResolutionHomologySurjective` | `lem-pc-derived-total-resolution-homology-surjective` |
| `Sheaf.Paper.DerivedTotalResolutionQuasiIso` | `lem-pc-derived-total-resolution-quasi-iso` |
| `Sheaf.Paper.HigherDirectImagePresheaf` | `lem-weil-pbc-higher-direct-image-presheaf` |
| `Sheaf.Paper.LocalizedCohomologyMayerVietoris` | `lem-sc-invert-s-cohomology-mayer-vietoris-diagram` |
| `Sheaf.Paper.NonvanishingSectionTrivializes` | `lem-weil-pbc-nonvanishing-section-trivializes` |
| `Sheaf.Paper.PQFCohomology` | `pqf-def-cohomology` |
| `Sheaf.Paper.TotalResolutionCycleFiniteSupport` | `aux-total-resolution-cycle-finite-support` |
| `Sheaf.Paper.TotalResolutionCycleReduction` | `lem-pc-derived-total-resolution-column-zero-cycle-reduction` |
| `Sheaf.Paper.TotalResolutionCycleSupportStep` | `aux-total-resolution-cycle-support-step` |
| `Sheaf.Paper.TotalResolutionCycleSupportZero` | `aux-total-resolution-cycle-support-zero` |
| `Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree` | `lem-sc-zariski-module-abelian-cohomology-agree` |
| `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` | `lem-sc-module-abelian-zariski-cohomology`, `new-zariski-module-abelian-cohomology-components` |
| `Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership` | `lem-sc-affine-finite-projective-prime-membership` |
| `Sheaf.RingTheory.FiniteProjectivePrimeLocalFree` | `lem-weil-pbc-finite-projective-prime-local-free` |
| `Sheaf.RingTheory.FreePrimeMembership` | `lem-sc-free-prime-membership` |
| `Sheaf.Topology.CohomologyPresheafDerivedSectionsEvaluation` | `lem-pc-cohomology-presheaf-derived-sections-evaluation` |
| `Sheaf.Topology.DerivedLimitStalkInjective` | `lem-pc-ringed-space-derived-limit-stalk-injective` |
| `Sheaf.Topology.InverseImageStalk` | `lem-weil-pbc-topological-inverse-image-stalk` |
| `Sheaf.Topology.ModuleMayerVietoris` | `lem-sc-mayer-vietoris-ringed-space` |
| `Sheaf.Topology.OpenModuleCohomology` | `def-sc-open-module-cohomology` |
| `Sheaf.Topology.OpenModuleCohomologyLocalIso` | `lem-sc-open-module-cohomology-local-iso` |
| `Sheaf.Topology.OpenModuleDerivedSections` | `def-pc-open-module-derived-sections` |
| `Sheaf.Topology.PointwiseTruncationLimit` | `lem-pc-ringed-space-pointwise-truncation-limit` |
| `Sheaf.Topology.PointwiseTruncationLimitExists` | `lem-pc-ringed-space-pointwise-truncation-limit-exists` |
| `Sheaf.Topology.PointwiseTruncationLimitIsIso` | `lem-pc-ringed-space-pointwise-truncation-limit-isIso` |
| `Sheaf.Topology.PointwiseTruncationOpenStabilization` | `lem-pc-pointwise-truncation-open-stabilization` |
| `Sheaf.Topology.RestrictInjectiveResolution` | `lem-sc-ringed-space-restrict-injective-resolution` |
| `Sheaf.Topology.RingedSpaceModuleCohomology` | `def-sc-ringed-space-module-cohomology`, `def-sc-sheaf-cohomology-functor` |
| `Sheaf.Topology.RingedSpaceModuleEnoughInjectives` | `lem-sc-ringed-space-module-sheaves-enough-injectives` |
| `Sheaf.Topology.RingedSpaceRGammaDerivedLimit` | `lem-pc-ringed-space-rgamma-derived-limit` |
| `Sheaf.Topology.SheafCokernelLocalImage` | `lem-weil-pbc-sheaf-cokernel-local-image` |
| `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.Bidual` | — |
| `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver` | — |
| `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit` | — |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual` | — |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree` | — |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver` | — |
| `WeilConjectures.Algebra.Homology.BifunctorLinear` | — |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided` | — |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure` | — |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom` | — |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.Products` | — |
| `WeilConjectures.Algebra.Homology.InternalHom` | — |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism` | `lem-pc-closed-immersion-coherent-cohomology` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech` | `lem-pc-affine-cech-complex`, `lem-pc-affine-vanishing` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic` | — |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` | `def-pc-scheme-module-flat-over`, `lem-pc-scheme-modules-grothendieck-abelian` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` | `lem-pc-cohomology-sections-affine-base`, `lem-pc-higher-direct-image-local-vanishing`, `lem-pc-projection-formula`, `lem-pc-sections-higher-direct-image-quasi-coherent`, `lem-pc-sections-open-base-change`, `new-higher-direct-image-affine-local-qcoherent` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque` | — |
| `WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero` | — |
| `WeilConjectures.AlgebraicGeometry.EffectiveCartier` | `def-pc-divisor-line-bundle`, `lem-pc-cartier-affine-generator-regular`, `lem-pc-divisor-line-bundle-flat-pullback`, `lem-pc-divisor-line-bundle-invertible`, `lem-pc-divisor-line-bundle-properties`, `lem-pc-recd-pullback` |
| `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` | `lem-pc-section-clearing-denominators` |
| `WeilConjectures.AlgebraicGeometry.Modules.Dual` | `lem-pc-tensor-dual-invertible`, `lem-sc-invertible-dual` |
| `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus` | `def-sc-section-generating-locus` |
| `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections` | `lem-sc-affine-invertible-sections` |
| `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` | `lem-pc-cokernel-finite-presentation-noetherian`, `lem-weil-pbc-quasi-coherent-module-cokernel-closure` |
| `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` | `def-pc-zero-scheme`, `lem-pc-invertible-common-free-generator`, `lem-pc-zero-scheme-divisor-iso`, `lem-pc-zero-scheme-ideal-local`, `lem-pc-zero-scheme-pullback-full-local-coefficient`, `lem-pc-zero-scheme-zero-iff`, `lem-sc-canonical-section-zero-scheme` |
| `WeilConjectures.CategoryTheory.Abelian.DimensionShifting` | — |
| `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` | `def-sp-acyclic`, `lem-weil-pbc-leray-acyclicity-quasi-iso` |
| `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence` | `lemma-weil-pbc-leray-acyclicity` |
| `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` | `lem-sc-source-kflat-tensor-left-triangulated` |
| `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction` | `prop-weil-pbc-derived-inverse-image-adjunction` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange` | `src-right-derived-functor-plus-base-change-of-right-acyclic` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility` | `src-right-derived-functor-plus-compatibility` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact` | — |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology` | `src-right-derived-functor-plus-acyclic-unit` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle` | `lem-sp-derived-functor-single-identification` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients` | — |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize` | — |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` | `lem-pc-derived-category-locally-small` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` | — |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` | — |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` | `lem-weil-pbc-sheaf-flat-separator` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits` | — |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` | `lem-weil-pbc-sheaf-tensor-closed` |
| `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` | — |
| `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided` | — |
| `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex` | — |
| `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` | — |
| `WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory` | — |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlus` | — |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf` | — |
| `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck` | `lem-sp-grothendieck-edge-maps`, `src-grothendieck-spectral-sequence-nat`, `thm-sp-grothendieck-base-change` |
| `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Pretriangulated` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.ShiftSequence` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.Monoidal` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.ObjectProperty` | — |
| `WeilConjectures.FromJoel.Algebra.Homology.Single` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedFour` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedThree` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor` | — |
| `WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.Composition` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesFour` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesThree` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Monoidal` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Product` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` | `def-pc-module-kflat-complex` |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Pentagon` | — |
| `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract` | — |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientThree` | — |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientTwo` | — |
| `WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor` | — |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` | — |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` | `lem-pc-total-bifunctor-comparison-iso` |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` | `lem-weil-pbc-derived-direct-image-triangulated`, `lem-weil-pbc-derived-functor-negative-vanishing` |
| `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.HomologySequence` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex` | — |
| `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` | — |
| `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` | `def-nagata-effective-cartier-ideal`, `def-nagata-invertible-ideal`, `lem-pc-flat-pullback-effective-cartier-ideal`, `lem-pc-nonzero-locally-principal-ideal-invertible`, `lemma-nagata-invertible-ideal-tensor-power` |
| `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow` | — |
| `WeilConjectures.Mathlib.CategoryTheory.EssentialImage` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided` | — |
| `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Orthogonal` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` | `lem-sp-right-adjoint-preserves-injectives` |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Shift.Localization` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` | `lem-galois-flasque`, `lem-weil-pbc-sheaf-ext-cohomology-long-exact` |
| `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` | `lem-weil-pbc-commshift-nattrans-triangle-morphism` |
| `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated` | — |
| `WeilConjectures.Mathlib.RingTheory.PicardGroup` | — |
| `WeilConjectures.Mathlib.Topology.Sheaves.Flasque` | — |
| `WeilConjectures.Topology.Sheaves.Cech` | `lem-pc-topological-injective-cech-positive-exact` |
| `WeilConjectures.Topology.Sheaves.CechCriterion` | `lem-pc-topological-ses-cech-sections-surjective` |
| `WeilConjectures.Topology.Sheaves.CechFlasque` | — |
| `WeilConjectures.Topology.Sheaves.PushforwardCohomology` | `lem-sc-topological-pushforward-injective` |
| `Sheaf.AlgebraicGeometry.FractionZeroTensorPower` | `lem-sc-section-affine-open-kills-cohomology-localization-step` |
| `Sheaf.CategoryTheory.SiteSesCechH1Surjective` | `lem-weil-pbc-site-ses-cech-h1-surjective` |
| `Sheaf.Topology.ModuleCohomologyTopComparison` | `lem-weil-pbc-module-cohomology-top-comparison` |

## Where the brief, the DAG or earlier work was wrong

Repair of return X-84d86: the earlier delivery copied six private declarations from
`PerfectHomTransport` (`cc_assoc`, `homMap_trTo`, `trTo_assoc`, `trTo_congr`,
`trTo_refl`, `tr_assoc`). This repair removes all six copies, along with copied private
`tr` and `trTo` definitions. Lean's `import all` makes the original private declarations
available, so the proof imports and uses them directly. No other module or visibility
is changed, and no forced adaptation is needed. The earlier second-reading section
was removed because it reviewed the superseded delivery; the repaired version needs
a fresh independent reading.


No mathematical error found. The original module imported the large push-pull cocone
branch even though its statement needs only PerfectHomTransport, and its original proof
plan did not need that cocone. The useful composition helpers in PerfectHomTransport
are private and are now reused directly through a proof-only `import all`.

Short-route searches: launcher LeanFinder for functorial conjugated Hom transport in a
cartesian square returned general categorical pullback lemmas, not this identity;
Loogle returned Functor.map_comp; launcher grep had no exact match. Direct repository
search located the private coherent transport calculations in PerfectHomTransport.
Read Stacks [0D5S](https://stacks.math.columbia.edu/tag/0D5S) for derived pullback
composition and [09RE](https://stacks.math.columbia.edu/tag/09RE) for the open Hom
comparison in the Mayer–Vietoris reduction. The proof supplies the coherence calculation
needed for that reduction, not the Hom-colimit isomorphism itself.

## Second reading by V1

1. Compared the entire delivered Lean module with the repository version and checked the
   existing theorem signature byte for byte: identical, including its let-bound canonical
   comparisons. Its docstring and visibility are unchanged. The node changes only `proof`
   and `proof_origin`; the declared public-import change has its change record. Pass.
2. Compiled the actual module cleanly (14.6 seconds). Compiled a fresh scratch copy with
   `#print axioms` for all three new private helpers and the public theorem (12.6 seconds):
   each uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Scanned
   the delivered Lean for forbidden declarations and holes: none. No data definition was
   added, and the proof constructs its cartesian arrows and local morphisms explicitly.
   Pass.
3. No statements are split off and no holes are added. The three private calculations are
   proved, strictly intermediate identities. Read the existing private transport lemmas
   in PerfectHomTransport and confirmed they are reused rather than copied. Independent
   grep, Loogle and LeanFinder searches found naturality laws already used by the proof,
   but no replacement for the whole coherence calculation. Identity arrows, empty opens
   and zero objects require no extra hypothesis: the argument uses functor laws, comparison
   cancellation and the cartesian universal property uniformly. Pass.
4. Read the proof downward: the square of cartesian arrows gives `ht`, composition
   coherence gives `hd`, expansion gives `norm`, and naturality gives the final equation.
   Both public imports are needed by the statement; `import all` is private to the proof.
   Checked both direct importers and their independent public cocone imports: no adaptation
   is required. The unit's `realized` statement and step lists are empty, so no realized
   route is bypassed. Recomputed the item-local import-closure difference: 545 modules.
   All three original proof dependencies remain used. Pass after the report repair below.
5. Compared the node proof steps and dependencies with the Lean calculations, including
   the imported associativity theorem and restriction data. They agree; the unchanged
   `proof_deps` is precisely the union of the proof-step uses. No new nodes. Pass.

Second reading changed documentation only: inserted the omitted proof-only `import all`
into the change record's New block; refreshed six rows of the pruning table against the
current repository (three obsolete rows removed, three current rows added); corrected the
report's dependency status to the verified axiom result; refreshed the change record's
downstream users after the dry run fetched a second direct importer. The Lean proof
needed no repair.
