## What changed

The original declaration and its public imports are unchanged. Its proof now constructs a fixed
normalized quotient model, constructs the CE second filtrations and their filtered total lifts,
then transports the canonical comparison along the supplied isomorphisms c. A proved private
page-two extensionality lemma upgrades the resulting page-two naturality square to equality of
entire spectral-sequence morphisms.

Repair of the landing return: removed the three duplicated private helpers
`subobject_preserves_pullback`, `subobject_preserves_inf`, and `filtered_step_preserved`
from `FilteredComplexDecalage`. A proof-only
`import all Sheaf.CategoryTheory.FilteredQuotientPageMaps` makes the existing private
lemmas available; the decalage proof now applies them directly. The import is acyclic,
and these helpers impose no finiteness assumption. Their source module was already
in the delivered import closure through the canonical sequence/model modules. The
decalage node now records this proof dependency. No existing library module, signature,
or visibility was changed by the repair, and no additional hole was introduced.

The new modules contain the following parts of this argument:

- `FilteredComplexCanonicalSequence`: actual differentials, normalized successor isomorphisms,
  coherent quotient maps and the page-two functor for arbitrary filtered cochain complexes.
- `FilteredComplexCanonicalModel`: actual cokernel quotient maps, uniquely normalized
  quotient-image isomorphisms, and proofs of every `FilteredPageTwoModel` field.
- `CartanEilenbergFilteredTotalLifts`: second filtrations and filtered lifts, proved directly
  from naturality of total summands and finite suprema of their images.
- `FilteredComplexDecalage`: the unique functorial decalage filtration, constructed as
  differential inverse images intersected with the shifted filtration steps, and its actual
  endofunctor with unchanged underlying complexes and maps.
- `LeftExactTruncationIso`: the unique inclusion-compatible isomorphism commuting an additive
  left exact functor with upper smart truncation, using its cycles kernel at the boundary.
- `CartanEilenbergTruncationResolution`: unique truncated bicomplex and total augmentations,
  their coordinate equations, quasi-isomorphism, injective total terms, vanishing below zero,
  K-injectivity, and their naturality for every CE presentation comparison. The total flip
  isomorphism retains the original unflipped total convention.
- `CartanEilenbergDerivedTruncationCohomology`: the mapped truncated total computes derived
  cohomology of the upper truncation in every integer cohomological degree.
- `CartanEilenbergCanonicalTruncationComparison`: the remaining comparison, for the fixed
  normalized model, with page-two naturality. It has one named theorem hole.

All choices of differentials, successor isomorphisms, quotient maps and image comparisons use
proved uniqueness theorems. There is no data definition depending on an unproved arbitrary
existence witness. No existing statement, definition or target was changed. The original
node's proof, proof dependencies and proof origin now describe the implemented route.

## Proved and sorry left

Closed the original hole:

- `CategoryTheory.exists_cartanEilenberg_filtered_truncation_comparison`
  (`lem-sp-ce-filtered-truncation-comparison`). Its proof is complete and has no local hole.

Added one hole:

- `CategoryTheory.cartanEilenberg_canonical_truncation_comparison`
  (`lem-sp-ce-canonical-truncation-comparison`), in its own module, exactly `:= by sorry`.

This is a decomposition: one upper hole is closed and one strictly smaller comparison hole is
added. It is not a completed proof of the CE/truncation comparison. The new hole has no
external sequence functor E, no quotient-model construction, no filtration construction and
no filtered-lift existence obligation; it asks only for the comparison of the fixed canonical
model and its page-two square. The final composition with arbitrary c, and its extension to
all pages, are proved in the original module.

The other new modules contain no holes. In particular the following constructions and results
are proved:

- `CategoryTheory.filteredComplexCanonicalPageTwoFunctor`, including uniqueness of its maps,
  differential compatibility, normalized successor compatibility, identity and composition.
- `CategoryTheory.filteredComplexCanonicalModel`, including its differential and map axioms.
- `CategoryTheory.cartanEilenberg_filtered_total_lifts`.
- `CategoryTheory.DecreasingFiltration.exists_decalage`, its degreewise formula, and
  `CategoryTheory.DecreasingFiltration.decalageFunctor`.
- `CategoryTheory.leftExact_truncation_iso`.
- `CategoryTheory.cartanEilenberg_truncation_resolution`.
- `CategoryTheory.cartanEilenberg_derived_truncation_cohomology`.

The model, lift and truncation-resolution constructions have been checked with `#print axioms`;
only `propext`, `Classical.choice` and `Quot.sound` occur. The delivery dry run checks every
submitted module. The remaining hole is the only newly submitted theorem using `sorry`.

The remaining comparison still needs:

1. Starting with the proved unique functorial decalage filtration, identify its subcomplex at -q with the horizontal smart-truncation total, and
   transport this identification through G. The left-exact truncation and finite mapped-total
   comparisons are proved; the identification with the CE truncation remains.
2. Assemble the derived truncation diagram comparison, including compatibility between
   different truncation indices and the representation of RF(P.X) by F(P.J). The truncated
   injective resolutions, their presentation-comparison squares and their objectwise derived
   cohomology computations are proved.
3. Prove the decalage page shift on the explicit cycle/boundary quotients at every page,
   including the representative differential and normalized successor homology equations.
4. Normalize the page-two interval-cohomology comparison and its naturality, including the
   total signs. The existing proved left-exact cohomology calculation is retained for this.

These are the remaining tasks in the single comparison node; the new resolved construction
nodes require no subsequent proof work.

## No longer needed

The repair also prunes the three duplicate private helper declarations from
`FilteredComplexDecalage`; their proofs are supplied by the existing declarations
in `FilteredQuotientPageMaps`. No module is newly pruned by this repair.

Removed from the original module's proof imports:

- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`
  (`lem-sp-filtered-complex-ZB-description`). Its globally finite filtration theorem is
  unnecessary for the explicit quotient model.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`
  (`lem-sp-cartan-eilenberg-comparison-independence`). Filtered total lifts are constructed
  directly. Their naturality is obtained from the comparison square, without an abutment or
  homotopy-independence theorem.
- The direct import `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
  (`lem-sp-cart-eilenberg-left-exact-cohomology`); this module remains a dependency of the
  remaining comparison and is not counted as transitively pruned.
- `def-sp-cartan-eilenberg-presentation` leaves the parent node's `proof_deps` but remains
  in its `stmt_deps` and public imports, and in the lift node's proof dependencies; its
  module is retained. This is dependency reclassification, not module pruning.

The complete list below is the difference of this item's old and new non-Mathlib import
closures, computed from actual imports with `tools/leanindex.py` comment stripping. Modules
still reached by the new route are excluded. These are item-local dependency removals;
other parents may continue using them. The maintainer's pinned sorry ledger determines the
project-wide progress figures. No node or library module is withdrawn by this delivery.

<details>
<summary>Complete modules and attached nodes no longer needed by this item</summary>

- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat` — `lem-weil-pbc-filtered-colimit-flat-modules`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension` — `lem-pc-sites-module-sheafification-bilinear-extension`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence` — `lem-pc-sites-module-sheafification-bilinear-extension-existence`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness` — `lem-pc-sites-module-sheafification-bilinear-extension-uniqueness`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat` — `lem-pc-sites-modules-sheafification-flat`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor` — `lem-pc-sites-module-sheafification-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback` — `lem-pc-presheaf-module-inverse-image-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison` — `lem-pc-topological-module-pullback-comparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives` — `lem-pc-topological-pullback-common-representatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction` — `lem-pc-module-change-of-rings-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` — source-library module
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct` — `lem-pc-sites-modules-coproduct-flat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule` — `def-pur-sheaf-modules-hom-module`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings` — `lem-weil-pbc-stalk-change-of-rings-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRingsPresheaf` — `lem-weil-pbc-presheaf-stalk-change-of-rings-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor` — `lem-pc-ringed-space-module-stalk-tensor`, `lem-weil-pbc-module-stalk-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` — `lem-pc-sites-sheaf-tensor-bilinear-universal`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` — `lem-pc-sheaf-modules-tensor-closed`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction` — `lem-weil-pbc-module-tensor-hom-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` — source-library module
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback` — `lem-pc-module-inverse-image-adjunction`
- `Sheaf.Algebra.FinitePresentationColimit` — `lem-pc-fp-module-map-descent-affine`
- `Sheaf.Algebra.FinitePresentationRestrictedHomColimit` — `lem-pc-fp-restricted-hom-colimit`
- `Sheaf.Algebra.FiniteRelationCokernelColimit` — `lem-pc-finite-relation-cokernel-colimit`
- `Sheaf.Algebra.FiniteRelationMatrixLift` — `lem-pc-finite-relation-matrix-lift`
- `Sheaf.Algebra.FiniteRelationQuotientComparison` — `lem-pc-finite-relation-quotient-comparison`
- `Sheaf.Algebra.FiniteTensorVanishingColimit` — `lem-pc-finite-tensor-vanishing-colimit`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor` — `lem-pur-acyclic-kflat-tensor-arbitrary`
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` — `lem-pc-bounded-above-flat-kflat`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` — `lem-pc-bounded-above-flat-kflat-site`
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic` — `lem-pc-bounded-above-flat-tensor-acyclic`
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree` — `lem-pc-bounded-above-flat-tensor-acyclic-degree`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat` — `lem-pc-module-bounded-flat-kflat`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement` — `lem-pc-kflat-bounded-flat-replacement`
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat` — `lem-pur-change-of-rings-acyclic-kflat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso` — `lem-pur-change-of-rings-kflat-quasi-iso`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorAcyclic` — `lem-pur-change-of-rings-tensor-acyclic`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison` — `lem-pur-change-of-rings-tensor-comparison`
- `Sheaf.Algebra.Homology.CyclePullbackCore` — `lem-pc-functorial-cycle-pullback-core-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackLaws` — `lem-pc-cycle-pullback-tower-laws-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackLifting` — `lem-pc-functorial-cycle-pullback-lifting-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackResolution` — `lem-pc-functorial-cycle-pullback-construction`
- `Sheaf.Algebra.Homology.CyclePullbackTower` — `def-pc-cycle-pullback-tower-data-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackTowerComparison` — `def-tower-canonical-comparison-g3`, `lem-pc-cycle-pullback-tower-comparison-stage3`, `new-tower-comparison-first`, `new-tower-comparison-second`
- `Sheaf.Algebra.Homology.DerivedChangeOfRings` — source-library module
- `Sheaf.Algebra.Homology.FilteredColimitsTensor` — `lem-pc-module-filtered-colimits-tensor`
- `Sheaf.Algebra.Homology.FilteredColimitsTensorTotal` — `lem-pc-module-filtered-colimits-tensor-preserves`
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription` — `lem-sp-filtered-complex-ZB-description`
- `Sheaf.Algebra.Homology.FinitePresentationPreorderColimitModel` — `lem-pc-fp-preorder-colimit-model`
- `Sheaf.Algebra.Homology.FirstQuadrantAugmentation` — `lem-sc-first-quadrant-column-augmentation`
- `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison` — `lem-sc-first-quadrant-total-column-comparison`
- `Sheaf.Algebra.Homology.FirstQuadrantTotalComparisonFinite` — `lem-sc-finite-row-total-column-comparison`
- `Sheaf.Algebra.Homology.FirstQuadrantTotalExtension` — `lem-sc-total-extension-nat-arrow-iso`
- `Sheaf.Algebra.Homology.FlatAugmentationEpicification` — `lem-pc-flat-augmentation-epicification`
- `Sheaf.Algebra.Homology.FlatCoverFunctor` — `lem-pc-sites-modules-functorial-flat-cover`
- `Sheaf.Algebra.Homology.FlatTruncationSuccessor` — `lem-pc-flat-truncation-successor`
- `Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison` — `lem-pc-flat-truncation-telescope-comparison`
- `Sheaf.Algebra.Homology.FlatTruncationTower` — `lem-pc-flat-truncation-tower`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransport` — `lem-pc-ringed-inverse-image-stalk-scalar-transport`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta` — `lem-pc-ringed-inverse-image-stalk-scalar-transport-beta`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality` — `lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality`
- `Sheaf.Algebra.Homology.KFlat` — `def-pc-kflat-complex`
- `Sheaf.Algebra.Homology.KFlatClosure` — `lem-pc-kflat-cone-direct-sum`
- `Sheaf.Algebra.Homology.KFlatModuleBaseChange` — `lem-pc-kflat-extension-of-scalars`
- `Sheaf.Algebra.Homology.KFlatPullback` — `lem-pc-kflat-pullback-preservation`
- `Sheaf.Algebra.Homology.KFlatResolution` — source-library module
- `Sheaf.Algebra.Homology.KFlatStalkCriterion` — `lem-pc-kflat-stalk-criterion`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure` — `lem-pc-kflat-closure`
- `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree` — `lem-pc-kflat-tensor-cone-two-out-of-three`
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` — `lem-sc-derived-k-injective-restrict-open`
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` — `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkOutside` — `lem-sc-module-extension-by-zero-stalk-maps-outside`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitEpi` — `lem-sc-module-extension-by-zero-unit-epi`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitFaithful` — `lem-sc-module-extension-by-zero-unit-mono-faithful-aux`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitIsIso` — `lem-sc-module-extension-by-zero-unit-isiso`
- `Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitMono` — `lem-sc-module-extension-by-zero-unit-mono`
- `Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents` — `new-module-restriction-stalk-components`
- `Sheaf.Algebra.Homology.ModuleStalkExact` — `lem-weil-pbc-module-stalk-exact`
- `Sheaf.Algebra.Homology.ModuleStalkFunctor` — `def-pc-module-stalk-functor`
- `Sheaf.Algebra.Homology.OpenCoverAdjunctionTriangle` — `lem-sc-open-cover-adjunction-triangle`
- `Sheaf.Algebra.Homology.OpenCoverMateComplexShortExact` — `lem-sc-open-cover-mate-complex-short-exact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExact` — `lem-sc-open-cover-mate-module-short-exact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExactCore` — `lem-sc-open-cover-mate-module-counit-compatibility`, `lem-sc-open-cover-mate-module-short-exact-core`
- `Sheaf.Algebra.Homology.OpenDerivedMatePresentation` — `lem-sc-localization-nested-adjunction-mate`
- `Sheaf.Algebra.Homology.OpenExtensionCounitStalk` — `lem-sc-open-extension-counit-stalk`
- `Sheaf.Algebra.Homology.OpenHomTriangleRealization` — `lem-sc-open-hom-triangle-realization`
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` — `lem-sc-derived-open-restriction-adjunction-exact`
- `Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated` — `lem-pur-quasi-isos-saturated-triangulated`
- `Sheaf.Algebra.Homology.RelativeFlatExtension` — `lem-pc-relative-flat-extension`
- `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` — `lem-weil-pbc-ringed-space-module-exactness-local-lifting`
- `Sheaf.Algebra.Homology.SplitIdentityFromFunctionals` — `lem-weil-pbc-split-identity-from-functionals`
- `Sheaf.Algebra.Homology.SplitIdentityHomotopyEquiv` — `lem-pc-split-identity-homotopy-equiv`
- `Sheaf.Algebra.Homology.StalkTensorComplex` — `lem-pc-stalk-tensor-complex`
- `Sheaf.Algebra.Homology.StalkTensorComplexDegrees` — `lem-pc-stalk-tensor-complex-degrees`
- `Sheaf.Algebra.Homology.StalkTensorComplexDifferential` — `lem-pc-stalk-tensor-complex-differential`
- `Sheaf.Algebra.Homology.TelescopeColimit` — `lem-pc-complex-hocolim-colimit`
- `Sheaf.Algebra.Homology.TelescopeShiftMono` — `lem-pc-telescope-shift-mono`
- `Sheaf.Algebra.Homology.TensorPullbackStalkComplex` — `lem-pc-tensor-pullback-stalk-complex`
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalars` — `lem-pc-tensor-restrict-extend-scalars`
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule` — `lem-pc-tensor-restrict-extend-module-natural`
- `Sheaf.Algebra.Homology.TruncationTelescope` — `lem-pc-kflat-hocolim-truncations`
- `Sheaf.Algebra.Homology.TwoTermCoimageQuasiIso` — `lem-weil-pbc-two-term-coimage-quasiiso`
- `Sheaf.Algebra.Homology.UnitEntrySplits` — `lem-weil-pbc-free-complex-unit-entry-splits`
- `Sheaf.Algebra.Homology.UpperTruncationStepQuotient` — `lem-weil-pbc-upper-step-quotient-coordinates`
- `Sheaf.Algebra.Homology.UpperTruncationStepSES` — `lem-weil-pbc-truncation-step-ses`
- `Sheaf.Algebra.LimitFinitePresentation` — `lem-weil-pbc-limit-finite-presentation`
- `Sheaf.Algebra.LimitFinitePresentation.Colimits` — `lem-weil-pbc-limit-finite-presentation-colimits`
- `Sheaf.Algebra.LimitFinitePresentation.Core` — `lem-weil-pbc-limit-finite-presentation-core`
- `Sheaf.Algebra.TorOneSurjectiveChangeRings` — `lem-weil-pbc-tor-one-surjective-change-rings`
- `Sheaf.AlgebraicGeometry.AdditiveAlternatingCechCoordinates` — `lem-pc-additive-alternating-cech-coordinates`
- `Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps` — `lem-weil-pbc-affine-algebra-local-maps`
- `Sheaf.AlgebraicGeometry.AffineAlternatingCechModel` — `def-pc-affine-alternating-cech-model`
- `Sheaf.AlgebraicGeometry.AffineAssociatedModuleFlatOver` — `lem-pc-affine-associated-module-flat-over`
- `Sheaf.AlgebraicGeometry.AffineBaseChangeChartColimit` — `lem-pc-affine-base-change-chart-colimit`
- `Sheaf.AlgebraicGeometry.AffineBasePieceTensorBaseChange` — `lem-weil-pbc-affine-base-piece-tensor-base-change`
- `Sheaf.AlgebraicGeometry.AffineBasePieceTensorBaseChangeInstance` — `lem-weil-pbc-affine-base-piece-tensor-base-change-instance`
- `Sheaf.AlgebraicGeometry.AffineBasePieceTensorComparison` — `lem-weil-pbc-affine-base-piece-tensor-comparison`
- `Sheaf.AlgebraicGeometry.AffineBasePieceTensorPresentation` — `lem-weil-pbc-affine-base-piece-tensor-presentation`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpen` — `lem-sc-affine-cap-section-open`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpenAlgebra` — `lem-sc-affine-cap-section-open-algebra`
- `Sheaf.AlgebraicGeometry.AffineCapSectionOpenDictionary` — `lem-sc-affine-cap-section-open-dictionary`
- `Sheaf.AlgebraicGeometry.AffineChartCanonicalHomNaturality` — `lem-pc-affine-chart-canonical-hom-naturality`
- `Sheaf.AlgebraicGeometry.AffineChartNormalizedSectionModels` — `lem-pc-affine-chart-normalized-section-models`
- `Sheaf.AlgebraicGeometry.AffineChartOrdinaryHomComparison` — `lem-pc-affine-chart-ordinary-hom-comparison`
- `Sheaf.AlgebraicGeometry.AffineChartOrdinaryMapDescent` — `lem-pc-affine-chart-ordinary-map-descent`
- `Sheaf.AlgebraicGeometry.AffineChartRelativeFlatCriterion` — `lem-pc-affine-chart-relative-flat-criterion`
- `Sheaf.AlgebraicGeometry.AffineChartRingColimitGeometric` — `new-affine-chart-ring-colimit-geometric`
- `Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentations` — `lem-pc-affine-chart-section-ring-presentations`
- `Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentationsIso` — `new-affine-chart-section-ring-presentations-iso`
- `Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentationsTail` — `new-affine-chart-section-ring-presentations-tail`
- `Sheaf.AlgebraicGeometry.AffineChartSectionsColimitComparison` — `lem-pc-affine-chart-sections-colimit-comparison`
- `Sheaf.AlgebraicGeometry.AffineChartTensorRecovery` — `lem-pc-affine-chart-tensor-coordinate-recovery`
- `Sheaf.AlgebraicGeometry.AffineChartUpperTailLimit` — `new-affine-chart-upper-tail-limit`
- `Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitComparisons` — `new-affine-chart-upper-tail-limit-comparisons`
- `Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData` — `new-affine-chart-upper-tail-limit-data`
- `Sheaf.AlgebraicGeometry.AffineCompatibleDenominatorData` — `lem-weil-pbc-affine-compatible-denominator-data`
- `Sheaf.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion` — `lem-pc-affine-cover-module-tensor-flat-criterion`
- `Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest` — `lem-pc-affine-finite-type-pullback-zero-test`
- `Sheaf.AlgebraicGeometry.AffineFlatModuleDescent` — `lem-pc-affine-flat-module-descent`
- `Sheaf.AlgebraicGeometry.AffineFlatModuleStalkFlat` — `lem-pc-affine-flat-module-stalk-flat`
- `Sheaf.AlgebraicGeometry.AffineFlatModuleTensorFlat` — `lem-pc-affine-flat-module-tensor-flat`
- `Sheaf.AlgebraicGeometry.AffineFreeComplexModuleLift` — `lem-pc-affine-free-complex-module-lift`
- `Sheaf.AlgebraicGeometry.AffineFreeComplexUnitCancellation` — `lem-pc-affine-free-complex-unit-cancellation`
- `Sheaf.AlgebraicGeometry.AffineIdealGeneratorCover` — `lem-weil-pbc-affine-ideal-generator-cover`
- `Sheaf.AlgebraicGeometry.AffineIdealIntersectionInclusion` — `lem-pc-affine-ideal-intersection-inclusion`
- `Sheaf.AlgebraicGeometry.AffineIsomorphicSourceNormalizedModels` — `lem-pc-affine-isomorphic-source-normalized-models`
- `Sheaf.AlgebraicGeometry.AffineLocalizationSheafification` — `lem-pc-affine-localization-sheafification`
- `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf` — `lem-pc-affine-localizing-presheaf-basis-sheaf`
- `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification` — `lem-pc-affine-localizing-presheaf-sheafification`
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec` — `lem-weil-pbc-affine-morphism-relative-spec`
- `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalization` — `lem-sc-invert-s-cohomology-affine-open`
- `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalizationZero` — `lem-sc-invert-s-cohomology-affine-open-zero`
- `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem` — `lem-weil-pbc-affine-open-directed-ring-system`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing` — `pqf-lem-affine-vanishing`
- `Sheaf.AlgebraicGeometry.AffineOpenSectionFractionLocalization` — `lem-sc-affine-open-section-fraction-localization`
- `Sheaf.AlgebraicGeometry.AffineOpenTwistVanishingIndependent` — `lem-pc-q3-affine-open-twist-vanishing-independent`
- `Sheaf.AlgebraicGeometry.AffineOverLimitInclusion` — `lem-weil-pbc-affine-over-limit-inclusion`
- `Sheaf.AlgebraicGeometry.AffinePullbackChartTensorFlatStalks` — `lem-pc-affine-pullback-chart-tensor-flat-stalks`
- `Sheaf.AlgebraicGeometry.AffinePullbackChartTensorSections` — `lem-pc-affine-pullback-chart-tensor-sections`
- `Sheaf.AlgebraicGeometry.AffineRestrictedTwistVanishing` — `lem-pc-e4-affine-restricted-twist-fixed-degree`
- `Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension` — `lem-weil-pbc-affine-section-linear-map-extension`
- `Sheaf.AlgebraicGeometry.AffineSectionLocalization` — `lem-sc-affine-section-localization`
- `Sheaf.AlgebraicGeometry.AffineSectionZeroAtStage` — `lem-pc-affine-section-zero-at-stage`
- `Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel` — `lem-pc-affine-sheaf-resolution-from-ring-model`
- `Sheaf.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful` — `lem-weil-pbc-affine-structure-algebra-fully-faithful`
- `Sheaf.AlgebraicGeometry.AffineTopTensorSections` — `lem-sc-affine-top-tensor-sections`
- `Sheaf.AlgebraicGeometry.AlternatingCechComputes` — `lem-pc-alternating-cech-computes`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingBoundary` — `lem-pc-alternating-cech-first-sorting-boundary`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingIdentity` — `lem-pc-alternating-cech-first-sorting-identity`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingJunctionDeletions` — `lem-pc-alternating-cech-first-sorting-junction-deletions`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingNonjunctionCancellation` — `lem-pc-alternating-cech-first-sorting-nonjunction-cancellation`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingPrefixCancellation` — `lem-pc-alternating-cech-first-sorting-prefix-cancellation`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingPrefixContribution` — `lem-pc-alternating-cech-first-sorting-junction-prefix-contribution`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingTailCancellation` — `lem-pc-alternating-cech-first-sorting-tail-cancellation`
- `Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingTailContribution` — `lem-pc-alternating-cech-first-sorting-junction-tail-contribution`
- `Sheaf.AlgebraicGeometry.AlternatingCechKernelNullHomotopic` — `lem-pc-alternating-cech-kernel-null-homotopic`
- `Sheaf.AlgebraicGeometry.AlternatingCechPartialSortAdvance` — `lem-pc-alternating-cech-partial-sort-advance`
- `Sheaf.AlgebraicGeometry.AlternatingCechPartialSortUnique` — `lem-pc-alternating-cech-partial-sort-unique`
- `Sheaf.AlgebraicGeometry.AlternatingCechPrefixDeletionBijection` — `lem-pc-alternating-cech-prefix-deletion-bijection`
- `Sheaf.AlgebraicGeometry.AlternatingCechRepeatCentralFaces` — `lem-pc-alternating-cech-repeat-central-faces`
- `Sheaf.AlgebraicGeometry.AlternatingCechRepeatOuterFaces` — `lem-pc-alternating-cech-repeat-outer-faces`
- `Sheaf.AlgebraicGeometry.AlternatingCechRestrictionHomotopy` — `lem-pc-alternating-cech-restriction-homotopy`
- `Sheaf.AlgebraicGeometry.AlternatingCechSecondSortingIdentity` — `lem-pc-alternating-cech-second-sorting-identity`
- `Sheaf.AlgebraicGeometry.AlternatingCechSection` — `lem-pc-alternating-cech-section`
- `Sheaf.AlgebraicGeometry.AlternatingCechSortedContraction` — `lem-pc-alternating-cech-sorted-contraction`
- `Sheaf.AlgebraicGeometry.AlternatingCechSortingBoundaryTransport` — `lem-pc-alternating-cech-sorting-boundary-transport`
- `Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators` — `def-pc-alternating-cech-sorting-operators`
- `Sheaf.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence` — `lem-pc-alternating-cech-tail-deletion-basic`, `lem-pc-alternating-cech-tail-deletion-correspondence`, `lem-pc-alternating-cech-tail-deletion-junction`
- `Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex` — `def-sc-alternating-cech-total-complex`
- `Sheaf.AlgebraicGeometry.AmpleFinitePowerCover` — `lem-weil-pbc-ample-finite-common-power-cover`
- `Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase` — `lem-weil-pbc-ample-very-ample-immersion-affine-base`
- `Sheaf.AlgebraicGeometry.AmpleIso` — `lem-sc-ample-iso`
- `Sheaf.AlgebraicGeometry.AmpleSeparated` — `lem-weil-pbc-ample-scheme-separated`
- `Sheaf.AlgebraicGeometry.AnnihilatorAffineCriterion` — `lem-weil-pbc-annihilator-affine-criterion`
- `Sheaf.AlgebraicGeometry.AnnihilatorSubsheaf` — `lem-weil-pbc-annihilator-subsheaf-construction`
- `Sheaf.AlgebraicGeometry.BaseChangeConventions` — `def-pc-base-change`
- `Sheaf.AlgebraicGeometry.BirationalLinePushforwardGenericStalk` — `lem-pc-q2-birational-line-pushforward-generic-stalk`
- `Sheaf.AlgebraicGeometry.CechDifferentialPermutation` — `lem-pc-cech-differential-permutation`
- `Sheaf.AlgebraicGeometry.CechDifferentialRepeated` — `lem-pc-cech-differential-repeated`
- `Sheaf.AlgebraicGeometry.CechDifferentialRepeatedCancellation` — `lem-pc-cech-differential-repeated-cancellation`
- `Sheaf.AlgebraicGeometry.CechDifferentialRepeatedDecomposition` — `lem-pc-cech-differential-repeated-decomposition`
- `Sheaf.AlgebraicGeometry.CechEvaluationComparison` — `lem-pc-cech-evaluation-comparison`
- `Sheaf.AlgebraicGeometry.CechModuleSheafFunctor` — `def-pc-cech-module-sheaf-functor`
- `Sheaf.AlgebraicGeometry.CechModuleSheafTerms` — `lem-pc-cech-module-sheaf-terms`
- `Sheaf.AlgebraicGeometry.CechSheafLocalAugmentationKernel` — `lem-pc-cech-local-augmentation-kernel`
- `Sheaf.AlgebraicGeometry.CechSheafLocalPositiveExact` — `lem-pc-cech-local-positive-exact`
- `Sheaf.AlgebraicGeometry.CechSheafLocalPositiveSections` — `lem-pc-cech-local-positive-section-boundary`
- `Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso` — `lem-pc-cech-sheaf-local-quasi-iso`
- `Sheaf.AlgebraicGeometry.ChartOrdinaryMapRecovery` — `def-pc-chart-ordinary-map-recovery`
- `Sheaf.AlgebraicGeometry.ChartTensorPullbackComparisonCoherence` — `lem-pc-chart-tensor-pullback-comparison-coherence`
- `Sheaf.AlgebraicGeometry.ChartTensorPullbackLiftTransport` — `lem-pc-chart-tensor-pullback-lift-transport`
- `Sheaf.AlgebraicGeometry.ChowFiniteCohomologyWitness` — `lem-pc-v3-chow-finite-cohomology-witness`
- `Sheaf.AlgebraicGeometry.ChowFiniteType` — `lem-weil-pbc-chow-finite-type`
- `Sheaf.AlgebraicGeometry.ChowRelativeAmple` — `lem-pc-chow-relative-ample`
- `Sheaf.AlgebraicGeometry.ChowRelativeAmpleGeometric` — `lem-pc-chow-relative-ample-geometric`
- `Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwist` — `lem-pc-chow-relative-ample-twist`
- `Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistIso` — `lem-pc-chow-relative-ample-twist-iso`
- `Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistProperties` — `lem-pc-chow-relative-ample-twist-properties`
- `Sheaf.AlgebraicGeometry.ChowTwistFiniteCohomology` — `lem-pc-q2-chow-twist-finite-cohomology`
- `Sheaf.AlgebraicGeometry.ClosedChowStage` — `lem-weil-pbc-closed-chow-stage`
- `Sheaf.AlgebraicGeometry.ClosedFreeIdealProductIso` — `lem-pc-g1-closed-free-ideal-product-iso`
- `Sheaf.AlgebraicGeometry.ClosedImmersionFixedDegreeVanishing` — `lem-pc-c2-closed-immersion-fixed-degree-vanishing`
- `Sheaf.AlgebraicGeometry.ClosedImmersionTwistAcyclicPresentation` — `lem-pc-d2-closed-immersion-twist-acyclic-presentation`
- `Sheaf.AlgebraicGeometry.ClosedImmersionTwistCohomologyBound` — `lem-pc-j4-closed-immersion-twist-cohomology-bound`
- `Sheaf.AlgebraicGeometry.ClosedImmersionTwistVanishingStep` — `lem-pc-j4-closed-immersion-twist-vanishing-step`
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks` — `lem-weil-pbc-closed-pushforward-stalks`
- `Sheaf.AlgebraicGeometry.ClosedStructureAmbientIdealExtension` — `lem-pc-closed-structure-ambient-ideal-extension`
- `Sheaf.AlgebraicGeometry.ClosedStructureIdealProductIso` — `lem-pc-closed-structure-ideal-product-iso`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase` — `def-weil-pbc-closed-subset-proper-over-base`
- `Sheaf.AlgebraicGeometry.CoefficientComparisonConstruction` — `lem-pc-coefficient-section-map-linear`
- `Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismFaces` — `lem-pc-coefficient-comparison-morphism-faces`
- `Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismGenerator` — `lem-pc-coefficient-comparison-morphism-generator`
- `Sheaf.AlgebraicGeometry.CoefficientIntersectionRingData` — `def-pc-coefficient-intersection-ring-data`
- `Sheaf.AlgebraicGeometry.CoefficientIntersectionRingPushout` — `aux-pc-coefficient-intersection-ring-pushout`
- `Sheaf.AlgebraicGeometry.CoefficientIntersectionScalarDecomposition` — `lem-pc-coefficient-intersection-scalar-decomposition`
- `Sheaf.AlgebraicGeometry.CoefficientIntersectionSectionModel` — `aux-pc-coefficient-intersection-section-model`
- `Sheaf.AlgebraicGeometry.CoefficientSourceAffineTensorPresentation` — `lem-pc-coefficient-source-affine-tensor-presentation`
- `Sheaf.AlgebraicGeometry.CoefficientTargetAffineTensorPresentation` — `lem-pc-coefficient-target-affine-tensor-presentation`
- `Sheaf.AlgebraicGeometry.CoefficientTargetGeneratorScalar` — `lem-pc-coefficient-target-generator-scalar`
- `Sheaf.AlgebraicGeometry.CoefficientTargetScalarSpan` — `lem-pc-coefficient-target-scalar-span`
- `Sheaf.AlgebraicGeometry.CoefficientTargetSectionGenerators` — `lem-pc-coefficient-target-section-generators`
- `Sheaf.AlgebraicGeometry.CoefficientTargetTensorDecoder` — `aux-pc-coefficient-target-tensor-decoder`
- `Sheaf.AlgebraicGeometry.CoefficientTargetTensorInjective` — `lem-pc-coefficient-target-tensor-injective`
- `Sheaf.AlgebraicGeometry.CoefficientTargetTensorSurjective` — `lem-pc-coefficient-target-tensor-surjective`
- `Sheaf.AlgebraicGeometry.Coherent` — `pqf-def-coherent`
- `Sheaf.AlgebraicGeometry.CoherentAffineSectionsFinite` — `lem-weil-pbc-coherent-affine-sections-finite`
- `Sheaf.AlgebraicGeometry.CoherentCokernelRelations` — `lem-weil-pbc-coherent-cokernel-relations`
- `Sheaf.AlgebraicGeometry.CoherentCokernelRelationsLocal` — `lem-weil-pbc-coherent-cokernel-relations-local`
- `Sheaf.AlgebraicGeometry.CoherentExtensionRelations` — `lem-weil-pbc-coherent-extension-relations`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeKernelOver` — `lem-weil-pbc-coherent-finite-type-kernel-over`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` — `pqf-lem-coherent-ft-locnoeth`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel` — `lem-weil-pbc-coherent-finite-type-sub-kernel`
- `Sheaf.AlgebraicGeometry.CoherentGenericFilteredExtension` — `lem-pc-s3-coherent-generic-filtered-extension`
- `Sheaf.AlgebraicGeometry.CoherentGenericFilteredSource` — `lem-pc-s3-coherent-generic-filtered-source`
- `Sheaf.AlgebraicGeometry.CoherentGenericLocalFreeModel` — `lem-pc-c3-coherent-generic-local-free-model`
- `Sheaf.AlgebraicGeometry.CoherentIdealPowerStableAnnihilator` — `lem-pc-coherent-ideal-power-stable-annihilator`
- `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed` — `lem-pc-s3-coherent-ideal-power-supported-on-closed`
- `Sheaf.AlgebraicGeometry.CoherentIdealPowerTorsionFreeProduct` — `lem-pc-coherent-ideal-power-torsion-free-product`
- `Sheaf.AlgebraicGeometry.CoherentIdealProductIntersectionBound` — `lem-pc-coherent-ideal-product-intersection-bound`
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltration` — `def-weil-pbc-coherent-integral-filtration`
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationBiproductSucc` — `new-coherent-integral-filtration-biproduct-succ`
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationExtension` — `lem-weil-pbc-coherent-integral-filtration-extension`
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumZero` — `lem-weil-pbc-coherent-integral-filtration-ideal-sum-zero`
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIrreducibleSupport` — `lem-pc-s3-irreducible-support-filtration-step`
- `Sheaf.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood` — `lem-weil-pbc-coherent-integral-generic-free-neighbourhood`
- `Sheaf.AlgebraicGeometry.CoherentIteratedSliceRelations` — `lem-weil-pbc-coherent-iterated-slice-relations`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian` — `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` — `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`
- `Sheaf.AlgebraicGeometry.CoherentKernelConditionDescent` — `lem-weil-pbc-coherent-kernel-condition-descent`
- `Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing` — `lem-weil-pbc-coherent-kernel-condition-descent-local-generators`
- `Sheaf.AlgebraicGeometry.CoherentKernelConditionRestriction` — `lem-weil-pbc-coherent-kernel-condition-restriction`
- `Sheaf.AlgebraicGeometry.CoherentKernelIdealIntersectionBound` — `lem-pc-coherent-kernel-ideal-intersection-bound`
- `Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType` — `lem-weil-pbc-coherent-kernel-intersection-finite-type`
- `Sheaf.AlgebraicGeometry.CoherentLocalFreeIdealLattice` — `lem-pc-c3-coherent-local-free-ideal-lattice`
- `Sheaf.AlgebraicGeometry.CoherentLocalIsomorphism` — `lem-weil-pbc-coherent-local-isomorphism`
- `Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCore` — `lem-weil-pbc-coherent-module-finite-type-local-core`
- `Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover` — `lem-weil-pbc-coherent-module-finite-type-local-cover`
- `Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalRestrict` — `lem-weil-pbc-coherent-module-finite-type-local-restrict`
- `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover` — `lem-weil-pbc-coherent-module-local-on-open-cover`
- `Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension` — `lem-pc-coherent-open-map-tensor-extension`
- `Sheaf.AlgebraicGeometry.CoherentOpenSectionCarrier` — `lem-pc-coherent-open-section-carrier`
- `Sheaf.AlgebraicGeometry.CoherentPushforwardIdeal` — `lem-pc-r2-coherent-pushforward-ideal`
- `Sheaf.AlgebraicGeometry.CoherentReducibleSupportExactSequence` — `lem-pc-s3-coherent-reducible-support-exact-sequence`
- `Sheaf.AlgebraicGeometry.CoherentStalkMapExtends` — `lem-weil-pbc-coherent-stalk-map-extends`
- `Sheaf.AlgebraicGeometry.CoherentSupportAdicChain` — `lem-pc-s3-coherent-support-adic-chain`
- `Sheaf.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence` — `lem-pc-s3-coherent-support-vanishing-ideal-nilpotence`
- `Sheaf.AlgebraicGeometry.CohomologyFiniteExtension` — `lem-pc-e2-cohomology-finite-extension`
- `Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero` — `lem-sc-cohomology-fraction-eventually-zero`
- `Sheaf.AlgebraicGeometry.CohomologyFractionPresentation` — `def-sc-cohomology-fraction-presentation`
- `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing` — `lem-sc-invert-s-cohomology-gluing`
- `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux` — `lem-sc-invert-s-cohomology-gluing-aux`
- `Sheaf.AlgebraicGeometry.CokernelTuplePullbackLocalFreeCover` — `lem-weil-pbc-cokernel-tuple-pullback-local-free-cover`
- `Sheaf.AlgebraicGeometry.CommonGenericLatticeMaps` — `lem-pc-r2-common-generic-lattice-maps`
- `Sheaf.AlgebraicGeometry.DerivedCategory` — `def-pc-derived-category`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh` — `lem-pc-derived-direct-image-bounded-below-qcoh`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded` — `lem-pc-derived-direct-image-composition`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` — `lem-pc-restrict-derived-direct-image-open`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` — `def-pc-derived-open-restriction-maps`
- `Sheaf.AlgebraicGeometry.DerivedPullback` — `def-pc-derived-pullback`
- `Sheaf.AlgebraicGeometry.DescendAffine` — `lem-weil-pbc-descend-affine`
- `Sheaf.AlgebraicGeometry.DescendClosedImmersion` — `lem-weil-pbc-descend-closed-immersion`
- `Sheaf.AlgebraicGeometry.DescendFinite` — `lem-weil-pbc-descend-finite`
- `Sheaf.AlgebraicGeometry.DescendFiniteAffineBasePiece` — `lem-weil-pbc-descend-finite-affine-base-piece`
- `Sheaf.AlgebraicGeometry.DescendFiniteAffineOpen` — `lem-weil-pbc-descend-finite-affine-open`
- `Sheaf.AlgebraicGeometry.DescendMonomorphism` — `lem-weil-pbc-descend-monomorphism`
- `Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel` — source-library module
- `Sheaf.AlgebraicGeometry.EpiOverFunctor` — `lem-stage3-epi-over-functor`
- `Sheaf.AlgebraicGeometry.EtaleTensorSections` — `lem-sc-etale-qcoherent-presheaf-functorial`
- `Sheaf.AlgebraicGeometry.EventuallyAffine` — `lem-weil-pbc-eventually-affine`
- `Sheaf.AlgebraicGeometry.EventuallyProper` — `lem-weil-pbc-eventually-proper`
- `Sheaf.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap` — `lem-weil-pbc-descend-separated`
- `Sheaf.AlgebraicGeometry.FieldComplexHomotopyNormalForm` — `new-field-complex-homotopy-normal-form`
- `Sheaf.AlgebraicGeometry.FieldComplexSingleCohomology` — `new-field-complex-single-cohomology`
- `Sheaf.AlgebraicGeometry.FieldFibreHomology` — `new-field-fibre-homology`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechBaseChangeCoordinates` — `lem-pc-finite-affine-cech-base-change-coordinates`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientBaseChange` — `lem-pc-finite-affine-cech-coefficient-base-change`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonBijective` — `lem-pc-finite-affine-cech-coefficient-comparison-bijective`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap` — `lem-pc-finite-affine-cech-coefficient-comparison-map`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange` — `lem-pc-finite-affine-cech-intersection-base-change`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechModel` — `def-pc-finite-affine-cech-model`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechModelComparison` — `lem-pc-finite-affine-cech-model-comparison`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechModelFlatOver` — `lem-pc-finite-affine-cech-model-flat-over`
- `Sheaf.AlgebraicGeometry.FiniteAffineCechSectionBaseChange` — `lem-pc-finite-affine-cech-section-base-change`
- `Sheaf.AlgebraicGeometry.FiniteFreeChainMapStalkEquality` — `lem-pc-finite-free-chain-map-stalk-equality`
- `Sheaf.AlgebraicGeometry.FiniteFreeLocalHomZero` — `lem-weil-pbc-finite-free-local-hom-zero`
- `Sheaf.AlgebraicGeometry.FiniteFreeLocalStalkMapLift` — `lem-weil-pbc-finite-free-local-stalk-map-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeModuleStalkEquiv` — `lem-weil-pbc-finite-free-module-stalk-equiv`
- `Sheaf.AlgebraicGeometry.FiniteFreePullbackResidueCriterion` — `lem-pc-finite-free-pullback-residue-criterion`
- `Sheaf.AlgebraicGeometry.FiniteFreeResidueLocalHomotopy` — `lem-pc-finite-free-residue-local-homotopy`
- `Sheaf.AlgebraicGeometry.FiniteFreeResidueLocusOpen` — `lem-pc-finite-free-residue-locus-open`
- `Sheaf.AlgebraicGeometry.FiniteFreeResidueStalkHomotopy` — `lem-pc-finite-free-residue-stalk-homotopy`
- `Sheaf.AlgebraicGeometry.FiniteFreeReverseComponentsLift` — `lem-pc-finite-free-reverse-components-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre` — `lem-pc-finite-free-single-field-fibre`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkChainMapLift` — `lem-pc-finite-free-stalk-chain-map-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkChainMapLiftLocal` — `lem-pc-finite-free-stalk-chain-map-lift-local`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkChainMapLiftRestrict` — `lem-pc-finite-free-stalk-chain-map-lift-restrict`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkChainMapPairLift` — `lem-pc-finite-free-stalk-chain-map-pair-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLift` — `lem-pc-finite-free-stalk-degreewise-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftAux` — `lem-pc-finite-free-stalk-degreewise-lift-core-aux`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftCore` — `lem-pc-finite-free-stalk-degreewise-lift-core`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLocal` — `lem-pc-finite-free-stalk-degreewise-local`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseShrink` — `lem-pc-finite-free-stalk-degreewise-shrink`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteEquations` — `lem-pc-finite-free-stalk-finite-equations`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift` — `lem-pc-finite-free-stalk-finite-matrix-lift`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyPShrink` — `lem-pc-finite-free-stalk-homotopy-p-only`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyPairShrink` — `lem-pc-finite-free-stalk-homotopy-pair-shrink`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopyQShrink` — `lem-pc-finite-free-stalk-homotopy-q-inside`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopySpread` — `lem-pc-finite-free-stalk-homotopy-spread`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality` — `lem-pc-finite-free-stalk-map-eq-shrink`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkMapLocal` — `lem-pc-finite-free-stalk-map-local`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkMapPositive` — `lem-pc-finite-free-stalk-map-local-positive`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkMinimalComplex` — `lem-pc-finite-free-stalk-minimal-complex`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellation` — `lem-pc-finite-free-stalk-unit-cancellation`
- `Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellationAt` — `lem-pc-finite-free-stalk-unit-cancellation-at`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank` — `lem-sc-finite-locally-free-stalk-finrank`
- `Sheaf.AlgebraicGeometry.FinitePresentationAffineChartModels` — `lem-pc-fp-affine-chart-object-models`
- `Sheaf.AlgebraicGeometry.FinitePresentationAffineChartSectionsModel` — `lem-pc-fp-affine-chart-sections-model`
- `Sheaf.AlgebraicGeometry.FinitePresentationAffineSectionsRealization` — `lem-pc-fp-affine-sections-realization`
- `Sheaf.AlgebraicGeometry.FinitePresentationChartMapZeroEventually` — `lem-pc-fp-chart-map-zero-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration` — `lem-pc-e2-finite-presentation-integral-filtration`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalDescentDatum` — `lem-pc-fp-local-descent-datum`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum` — `lem-pc-fp-local-map-datum`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts` — `lem-pc-fp-local-map-lifts`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility` — `lem-pc-fp-local-map-overlap-compatibility`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` — `lem-pc-fp-local-map-overlap-equations`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapPairEventually` — `lem-pc-fp-local-map-pair-defect-zero`, `lem-pc-fp-local-map-pair-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapPairEventuallyCompositesCompatible` — `lem-pc-fp-local-map-pair-composites-compatible`, `lem-pc-fp-local-map-pair-composites-defect-zero-core`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapRecoveryTransport` — `lem-pc-fp-local-map-recovery-transport`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels` — `lem-pc-fp-local-object-models`
- `Sheaf.AlgebraicGeometry.FinitePresentationLocalOverlapModels` — `lem-pc-fp-local-overlap-models`
- `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` — `lem-pc-fp-module-map-descent`
- `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLift` — `lem-pc-fp-one-chart-map-lift`
- `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage` — `lem-pc-fp-one-chart-map-lift-at-stage`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations` — `lem-pc-fp-overlap-eventual-chart-equations`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence` — `lem-pc-fp-overlap-eventual-coherence`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually` — `lem-pc-fp-overlap-diagonal-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting` — `lem-pc-fp-overlap-map-lifting`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting` — `lem-pc-fp-overlap-pair-map-lifting`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage` — `lem-pc-fp-overlap-pair-single-stage`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually` — `lem-pc-fp-overlap-triple-canonical-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually` — `lem-pc-fp-overlap-triple-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleTransport` — `lem-pc-fp-overlap-triple-transport`
- `Sheaf.AlgebraicGeometry.FinitePresentationSectionAffineOpenVanishing` — `lem-pc-fp-section-affine-open-eventually-zero`
- `Sheaf.AlgebraicGeometry.FinitePresentationSourceStalk` — `lem-weil-pbc-finite-presentation-source-stalk`
- `Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel` — `lem-weil-pbc-finite-presentation-stalk-kernel`
- `Sheaf.AlgebraicGeometry.FinitePresentationStalkOfLocalPresentation` — `lem-weil-pbc-stalk-finite-presentation-of-local-presentation`
- `Sheaf.AlgebraicGeometry.FinitePresentationSupportReductionFiltration` — `lem-pc-s3-support-reduction-filtration`
- `Sheaf.AlgebraicGeometry.FinitePresentationTestMapZeroEventually` — `lem-pc-fp-test-map-zero-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapAffineOpen` — `lem-pc-fp-zero-map-affine-open-eventually`
- `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent` — `lem-pc-fp-zero-map-descent`
- `Sheaf.AlgebraicGeometry.FinitePushforwardFiniteType` — `lem-pc-f3-finite-pushforward-finite-type`
- `Sheaf.AlgebraicGeometry.FiniteTypeEpiImage` — `lem-weil-pbc-sheaf-finite-type-epi-image`
- `Sheaf.AlgebraicGeometry.FiniteTypeIdealModule` — `lem-pqf-finite-type-ideal-module`
- `Sheaf.AlgebraicGeometry.FiniteTypeKernelLocalGenerators` — `lem-weil-pbc-finite-type-kernel-local-generators`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleStalkFinite` — `lem-weil-pbc-finite-type-module-stalk-finite`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed` — `lem-weil-pbc-finite-type-module-support-closed`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` — `def-pc-restricted-resolution-sections`, `def-pc-section-cohomology-presheaf`, `def-weil-pbc-flat-base-change-open-choices`
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` — `lem-pc-flat-complex-derived-pullback`
- `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison` — `lem-pc-flat-model-finite-free-shortening-comparison`
- `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeConstruction` — `lem-pc-flat-model-finite-free-shortening-construction`
- `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeQuasiIso` — `lem-pc-flat-model-finite-free-quasi-iso`
- `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeShortening` — `lem-pc-flat-model-finite-free-shortening`
- `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeTruncation` — `lem-pc-flat-model-finite-free-truncation-zero`
- `Sheaf.AlgebraicGeometry.FlatModelOpcyclesFlat` — `lem-pc-flat-model-opcycles-flat-zero`
- `Sheaf.AlgebraicGeometry.FlatModuleDescentAffineCharts` — `lem-pc-flat-module-descent-affine-charts`
- `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage` — `lem-pc-flat-module-on-later-stage`
- `Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction` — `lem-pc-flat-over-affine-open-restriction`
- `Sheaf.AlgebraicGeometry.FlatSheafStalk` — `lem-pc-flat-sheaf-stalk-flat`
- `Sheaf.AlgebraicGeometry.FractionZeroTensorPower` — `lem-sc-section-affine-open-kills-cohomology-localization-step`
- `Sheaf.AlgebraicGeometry.GeneralIdealPowerAffineSections` — `lem-weil-pbc-general-ideal-power-affine-sections`
- `Sheaf.AlgebraicGeometry.GeneratingSectionsStalkSpan` — `lem-weil-pbc-generating-sections-stalk-span`
- `Sheaf.AlgebraicGeometry.GenericIdealStalkEmbeddingExtension` — `new-generic-ideal-stalk-embedding-extension`
- `Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing` — `lem-pc-higher-direct-image-affine-basis-vanishing`
- `Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction` — `lem-pc-higher-direct-image-open-restriction`
- `Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators` — `lem-pc-higher-direct-image-section-denominators`
- `Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion` — `lem-pc-higher-direct-image-section-torsion`
- `Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization` — `lem-pc-higher-image-cohomology-presheaf-localization`
- `Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation` — `lem-weil-pbc-coherent-hom-local-kernel-from-presentation`
- `Sheaf.AlgebraicGeometry.IdealDataRecursivePowerComparison` — `lem-pc-ideal-data-recursive-power-comparison`
- `Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange` — `lem-weil-pbc-ideal-multiplication-stalk-range`
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk` — `lem-weil-pbc-ideal-module-product-stalk`
- `Sheaf.AlgebraicGeometry.IdealPowerAffineDenominatorMap` — `lem-weil-pbc-ideal-power-affine-denominator-map`
- `Sheaf.AlgebraicGeometry.IdealPowerComplement` — `lem-weil-pbc-ideal-power-complement`
- `Sheaf.AlgebraicGeometry.IdealPowerNumeratorPresentation` — `lem-weil-pbc-ideal-power-numerator-presentation`
- `Sheaf.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection` — `lem-weil-pbc-ideal-power-quotient-affine-lifting-section`
- `Sheaf.AlgebraicGeometry.IdealPowerTensorImageLift` — `lem-pc-ideal-power-tensor-image-lift`
- `Sheaf.AlgebraicGeometry.IdealPowerTorsionFreeSectionCarrier` — `lem-pc-ideal-power-torsion-free-section-carrier`
- `Sheaf.AlgebraicGeometry.IdealPowerTorsionFreeSectionLifting` — `lem-pc-ideal-power-torsion-free-section-lifting`
- `Sheaf.AlgebraicGeometry.IdealPowerTorsionFreeSectionRestriction` — `lem-pc-ideal-power-torsion-free-section-restriction`
- `Sheaf.AlgebraicGeometry.IdealTensorMultiplicationKernelControl` — `lem-pc-ideal-tensor-multiplication-kernel-control`
- `Sheaf.AlgebraicGeometry.IdealTensorRestrictedMultiplicationImage` — `lem-pc-ideal-tensor-restricted-multiplication-image`
- `Sheaf.AlgebraicGeometry.InjectiveModuleCechAugmentation` — `lem-sc-injective-module-cech-augmentation`
- `Sheaf.AlgebraicGeometry.InjectiveModuleCechAugmentationPositive` — `lem-sc-injective-module-cech-augmentation-positive`
- `Sheaf.AlgebraicGeometry.InjectiveModuleCechAugmentationZero` — `lem-sc-injective-module-cech-augmentation-zero`
- `Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective` — `lem-sc-ringed-space-injective-restriction-surjective`
- `Sheaf.AlgebraicGeometry.IntegralIdealAffineSections` — `lem-weil-pbc-integral-scheme-ideal-generic-stalk-affine`
- `Sheaf.AlgebraicGeometry.IntegralIdealCommonSubmodule` — `lem-pc-a2-integral-ideal-common-submodule`
- `Sheaf.AlgebraicGeometry.IntegralIdealComparisonFiltrations` — `lem-pc-v3-integral-ideal-comparison-filtrations`
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk` — `lem-weil-pbc-integral-scheme-ideal-generic-stalk`
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalkEquivalences` — `lem-weil-pbc-integral-scheme-ideal-generic-stalk-stalk`
- `Sheaf.AlgebraicGeometry.IntegralIdealProperCohomology` — `lem-pc-e2-integral-ideal-proper-cohomology`
- `Sheaf.AlgebraicGeometry.IntegralIdealsCommonGenericLattice` — `lem-pc-r2-integral-ideals-common-generic-lattice`
- `Sheaf.AlgebraicGeometry.InternalHomGermZeroFiniteType` — `lem-weil-pbc-internal-hom-germ-zero-finite-type`
- `Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation` — `lem-pc-intrinsic-flat-module-stalk-tensor-presentation`
- `Sheaf.AlgebraicGeometry.InverseImageExactKFlat` — `lem-pc-inverse-image-exact-kflat-resolution`
- `Sheaf.AlgebraicGeometry.InverseImageModuleFunctor` — `lem-pc-inverse-image-module-functor-exact`
- `Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison` — `lem-pc-inverse-image-tensor-pullback-comparison`
- `Sheaf.AlgebraicGeometry.InvertSCOhomology` — `lem-sc-invert-s-cohomology`
- `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization` — `lem-sc-p1-invertible-section-localization`
- `Sheaf.AlgebraicGeometry.LerayAcyclicAdditiveNaturality` — `lem-pc-k2-leray-acyclic-additive-naturality`
- `Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison` — `lem-pc-m1-leray-acyclic-pushforward-linear-comparison`
- `Sheaf.AlgebraicGeometry.LeraySectionsResolutionComparison` — `lem-pc-leray-sections-resolution-comparison`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition` — `lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-limit-affine-transition-affine-comparison`, `lem-weil-pbc-limit-affine-transition-core`
- `Sheaf.AlgebraicGeometry.LinearCechSheafConstruction` — `lem-pc-linear-cech-sheaf-construction`
- `Sheaf.AlgebraicGeometry.LinearCechSheafResolution` — `lem-pc-linear-cech-sheaf-resolution`
- `Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension` — `lem-pc-local-closed-ideal-map-extension`
- `Sheaf.AlgebraicGeometry.LocalMapPairCompatibility` — `def-pc-local-map-pair-compatibility`
- `Sheaf.AlgebraicGeometry.LocalMapPairDefect` — `def-pc-local-map-pair-defect-zero`
- `Sheaf.AlgebraicGeometry.LocalMapPairOverlapBaseChange` — `lem-pc-local-map-pair-overlap-base-change`
- `Sheaf.AlgebraicGeometry.LocalMapPullbackFamily` — `def-pc-local-map-pullback-family`
- `Sheaf.AlgebraicGeometry.LocalMapRecovery` — `def-pc-local-map-recovery`
- `Sheaf.AlgebraicGeometry.LocalMapRecoveryComposition` — `lem-pc-local-map-recovery-composition`
- `Sheaf.AlgebraicGeometry.LocalModuleEpiGermLift` — `lem-weil-pbc-local-module-epi-germ-lift`
- `Sheaf.AlgebraicGeometry.LocalOverlapTransitions` — `def-pc-local-overlap-transitions`
- `Sheaf.AlgebraicGeometry.LocalStalkFactorizationGermComparison` — `lem-weil-pbc-local-stalk-factorization-germ-comparison`
- `Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound` — `lem-pc-local-uniform-higher-direct-image-bound`
- `Sheaf.AlgebraicGeometry.LocalizingPrincipalCoverGluing` — `lem-pc-localizing-principal-cover-gluing`
- `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology` — source-library module
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction` — `lem-weil-pbc-module-base-change-map-open-restriction`
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso` — `lem-weil-pbc-module-open-square-isiso`
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes` — `lem-weil-pbc-module-square-restriction-commutes`
- `Sheaf.AlgebraicGeometry.ModuleBinaryLocalProperties` — `lem-weil-pbc-module-binary-local-properties`
- `Sheaf.AlgebraicGeometry.ModuleCechComparison` — `def-sc-module-cech-comparison`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion` — `lem-weil-pbc-module-cech-vanishing-criterion`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` — `def-weil-pbc-module-cohomology-fmap`
- `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison` — `lem-sc-module-cohomology-source-comparison`
- `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalLift` — `lem-weil-pbc-module-finite-free-local-lift`
- `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalSupport` — `lem-weil-pbc-module-finite-free-local-support`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineCapture` — `lem-weil-pbc-module-finite-type-affine-capture`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineEnlargement` — `lem-weil-pbc-module-finite-type-affine-enlargement`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators` — `lem-weil-pbc-module-finite-type-affine-generators`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineUnion` — `lem-weil-pbc-module-finite-type-affine-union`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeApproximation` — `lem-weil-pbc-module-finite-type-global-approximation`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension` — `lem-weil-pbc-module-finite-type-image-extension`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension` — `lem-weil-pbc-module-finite-type-submodule-extension`
- `Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsCompactSelection` — `lem-weil-pbc-module-generating-sections-compact-selection`
- `Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection` — `lem-weil-pbc-module-generating-sections-local-selection`
- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic` — `lem-weil-pbc-module-injective-open-cover-cech-acyclic`
- `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives` — `lem-weil-pbc-module-open-restriction-injectives`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineChartUnit` — `lem-weil-pbc-module-pullback-affine-chart-unit`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` — `lem-weil-pbc-module-pullback-affine-sections`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSectionsBijective` — `lem-weil-pbc-module-pullback-affine-sections-bijective`
- `Sheaf.AlgebraicGeometry.ModulePullbackFiniteType` — `lem-weil-pbc-module-pullback-finite-type`
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor` — `lem-weil-pbc-module-pullback-tensor`
- `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic` — `lem-weil-pbc-module-pushforward-injective-acyclic`
- `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveCechVanishing` — `lem-weil-pbc-module-pushforward-injective-cech-vanishing`
- `Sheaf.AlgebraicGeometry.ModuleRecoveryComparisonIso` — `def-pc-module-recovery-comparison-iso`
- `Sheaf.AlgebraicGeometry.ModuleRestrictionStalkIso` — `lem-weil-pbc-module-restriction-stalk-iso`
- `Sheaf.AlgebraicGeometry.ModuleSectionsAcyclicOfCohomologyVanishing` — `lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing`
- `Sheaf.AlgebraicGeometry.ModuleSectionsPullbackIsoTransport` — `new-module-sections-pullback-iso-transport`
- `Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1` — `lem-weil-pbc-module-ses-cech-h1-surjective`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` — `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluing` — `lem-weil-pbc-module-submodule-binary-gluing`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingCore` — `def-weil-pbc-module-binary-submodule-pullback`, `lem-weil-pbc-module-binary-submodule-mono`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingProperties` — `lem-weil-pbc-module-submodule-binary-gluing-restrictions`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingSecondRestriction` — `lem-weil-pbc-module-submodule-binary-gluing-second-restriction`
- `Sheaf.AlgebraicGeometry.ModuleSupportRestrictionEnlargement` — `lem-weil-pbc-module-support-restriction-enlargement`
- `Sheaf.AlgebraicGeometry.ModuleUnitLocalSupport` — `lem-weil-pbc-module-unit-local-support`
- `Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity` — `lem-pc-affine-extension-section-surjectivity`
- `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor` — `lem-weil-pbc-affine-tilde-tensor`
- `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk` — `lem-weil-pbc-affine-tilde-tensor-stalk-bijective`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction` — `lem-weil-pbc-module-extension-by-zero-adjunction`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula` — `lem-weil-pbc-module-extension-by-zero-hom-formula`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroInside` — `new-extension-by-zero-inside-stalk`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroOutside` — `new-extension-by-zero-outside-stalk`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroUnitStalks` — `lem-weil-pbc-module-extension-by-zero-unit-stalks`
- `Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact` — `lem-sc-ext-tensor-exact`
- `Sheaf.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport` — `lem-pc-inverse-image-stalk-scalar-transport`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` — `lem-weil-pbc-invertible-pullback-tensor`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` — `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum` — `lem-weil-pbc-quasi-coherent-module-direct-sum`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension` — `lem-pc-quasi-coherent-extension`
- `Sheaf.AlgebraicGeometry.Modules.ResidueFiber` — `def-weil-pbc-module-residue-fiber`
- `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison` — `lem-weil-pbc-module-restriction-tensor-comparison`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` — `lem-weil-pbc-module-stalk-pullback`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso` — `lem-weil-pbc-module-pullback-tensor-iso-criterion`
- `Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage` — `lem-pc-noetherian-proper-bounded-coherent-image`
- `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules` — `lem-weil-pbc-noetherian-acc-quasi-coherent`
- `Sheaf.AlgebraicGeometry.NonnegativeProjectiveTwistVanishing` — `lem-pc-d2-nonnegative-projective-twist-vanishing`
- `Sheaf.AlgebraicGeometry.NonvanishingCommonDegree` — `lem-weil-pbc-nonvanishing-common-degree`
- `Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` — `lem-sc-nonvanishing-iff-generates-at`
- `Sheaf.AlgebraicGeometry.NonvanishingLocusRestrict` — `lem-sc-nonvanishing-locus-restrict`
- `Sheaf.AlgebraicGeometry.NonvanishingTensorPullback` — `lem-sc-nonvanishing-tensor-pullback`
- `Sheaf.AlgebraicGeometry.NonvanishingTransitionFunctions` — `lem-weil-pbc-nonvanishing-transition-functions`
- `Sheaf.AlgebraicGeometry.OpenCohomologyFractionZeroComparison` — `lem-sc-open-cohomology-fraction-zero-comparison`
- `Sheaf.AlgebraicGeometry.OpenCohomologyZeroRestriction` — `lem-sc-open-cohomology-zero-restriction`
- `Sheaf.AlgebraicGeometry.OpenCohomologyZeroSections` — `lem-sc-open-cohomology-zero-sections`
- `Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport` — `lem-pc-open-cover-map-lift-transport`
- `Sheaf.AlgebraicGeometry.OpenCoverRefinementComparisons` — `def-pc-open-cover-refinement-comparisons`
- `Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence` — `lem-pc-open-cover-tensor-comparison-coherence`
- `Sheaf.AlgebraicGeometry.OpenCoverTensorDescentComparisonCoherence` — `lem-pc-open-cover-tensor-descent-comparison-coherence`
- `Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison` — `def-pc-open-cover-tensor-pullback-comparison`
- `Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComposition` — `lem-pc-open-cover-tensor-pullback-composition`
- `Sheaf.AlgebraicGeometry.OpenCoverTensorRecoveryNormalization` — `lem-pc-open-cover-tensor-recovery-normalization`
- `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison` — `lem-pqf-open-module-cohomology-comparison`
- `Sheaf.AlgebraicGeometry.OpenPushforwardDerivedComparison` — `lem-pc-open-pushforward-derived-comparison`
- `Sheaf.AlgebraicGeometry.OpenSectionFractionPresentation` — `def-sc-open-section-fraction-presentation`
- `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjection` — `lem-pc-ordered-cech-degreewise-projection`
- `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential` — `lem-pc-ordered-cech-degreewise-projection-differential`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleComparison` — `lem-pc-ordered-cech-module-comparison`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleCoordinates` — `def-pc-ordered-cech-module-coordinates`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleFirstSortingBoundary` — `lem-pc-ordered-cech-module-first-sorting-boundary`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleKernelNullHomotopic` — `lem-pc-ordered-cech-module-kernel-null-homotopic`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionHomotopy` — `lem-pc-ordered-cech-module-projection-homotopy`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionLift` — `lem-pc-ordered-cech-module-projection-lift`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleRestrictionMap` — `lem-pc-ordered-cech-module-restriction-map`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleRetraction` — `lem-pc-ordered-cech-module-retraction`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleSecondSortingBoundary` — `lem-pc-ordered-cech-module-second-sorting-boundary`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleSecondSortingLift` — `lem-pc-ordered-cech-second-sorting-degreewise`
- `Sheaf.AlgebraicGeometry.OrderedCechModuleSignedSection` — `lem-pc-ordered-cech-module-signed-section`
- `Sheaf.AlgebraicGeometry.OrdinaryPullbackRefinementCoherence` — `lem-pc-ordinary-pullback-refinement-coherence`
- `Sheaf.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion` — `lem-weil-pbc-over-pullback-diagonal-closed-immersion`
- `Sheaf.AlgebraicGeometry.OverlapBaseChangeFormula` — `lem-pc-overlap-base-change-formula`
- `Sheaf.AlgebraicGeometry.OverlapComparisonRefinement` — `lem-pc-overlap-comparison-refinement`
- `Sheaf.AlgebraicGeometry.OverlapConjugateRestriction` — `lem-pc-overlap-conjugate-restriction`, `lem-pc-overlap-conjugate-restriction-explicit`
- `Sheaf.AlgebraicGeometry.OverlapIteratedComparisonRefinement` — `lem-pc-overlap-iterated-comparison-refinement`
- `Sheaf.AlgebraicGeometry.OverlapModelChartFactorization` — `lem-pc-overlap-model-chart-factorization`
- `Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons` — `def-pc-overlap-pair-canonical-comparisons`
- `Sheaf.AlgebraicGeometry.OverlapPairModelTransport` — `lem-pc-overlap-pair-model-transport`
- `Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence` — `lem-pc-fp-overlap-pair-refinement-persistence`
- `Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport` — `lem-pc-overlap-pair-square-chart-transport`
- `Sheaf.AlgebraicGeometry.OverlapPairTransitionsAssembly` — `lem-pc-overlap-pair-transitions-assembly`
- `Sheaf.AlgebraicGeometry.OverlapSingleChartRestriction` — `lem-pc-overlap-single-chart-restriction`
- `Sheaf.AlgebraicGeometry.OverlapStageModelRestriction` — `lem-pc-overlap-stage-model-restriction`
- `Sheaf.AlgebraicGeometry.OverlapUniversalTestCoherence` — `lem-pc-overlap-universal-test-coherence`
- `Sheaf.AlgebraicGeometry.PrefixDeletionExistence` — `new-prefix-deletion-existence`
- `Sheaf.AlgebraicGeometry.PrefixDeletionRestrictions` — `new-prefix-deletion-restrictions`
- `Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent` — `lem-pc-m1-projective-affine-finite-cohomology-independent`
- `Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible` — `lem-weil-pbc-projective-ample-invertible`
- `Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation` — `lem-pc-u3-projective-finite-cohomology-presentation`
- `Sheaf.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment` — `lem-pc-p2-projective-finite-source-cohomology-segment`
- `Sheaf.AlgebraicGeometry.ProjectiveGraphTwistVanishing` — `lem-pc-m1-projective-graph-twist-vanishing`
- `Sheaf.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent` — `lem-pc-m1-projective-pushforward-finite-type-independent`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFiniteCoordinates` — `lem-weil-pbc-projective-space-finite-coordinates`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso` — `lem-weil-pbc-projective-space-finite-index-iso`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexIsIso` — `lem-weil-pbc-projective-space-reindex-is-iso`
- `Sheaf.AlgebraicGeometry.ProjectiveTwistFiniteCohomology` — `lem-pc-m4-projective-twist-finite-cohomology`
- `Sheaf.AlgebraicGeometry.ProperCohomologyFiniteFreeResolution` — `lem-pc-proper-cohomology-finite-free-resolution`
- `Sheaf.AlgebraicGeometry.ProperFlatCechModel` — `lem-pc-proper-flat-cech-model`
- `Sheaf.AlgebraicGeometry.ProperFlatCohomologyData` — `lem-pc-proper-flat-cohomology-model-data`
- `Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` — `lem-pc-proper-flat-single-noetherian-descent`
- `Sheaf.AlgebraicGeometry.PullbackStalkRelativeFlatExtension` — `lem-pc-pullback-stalk-relative-flat-extension`
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorFlat` — `lem-pc-pullback-stalk-tensor-flat`
- `Sheaf.AlgebraicGeometry.PushforwardFinSumSuccIso` — `new-pushforward-fin-sum-succ-iso`
- `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso` — `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange` — `lem-weil-pbc-quasi-coherent-affine-section-base-change`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra` — `def-weil-pbc-quasi-coherent-algebra`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion` — `lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit` — `lem-weil-pbc-quasi-coherent-algebra-colimit`
- `Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen` — `lem-weil-pbc-quasi-coherent-extension-qc-open`
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine` — `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections` — `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation` — `lem-weil-pbc-quasi-coherent-module-colimit-evaluation`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections` — `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction` — `lem-sc-invert-s-cohomology-induction`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty` — `property-intersection-qc-affine`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` — `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `Sheaf.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension` — `lem-pc-quasicoherent-open-section-ideal-extension`
- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs` — `pqf-lem-pushforward-qcoh`
- `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom` — `lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent`
- `Sheaf.AlgebraicGeometry.QuasicoherentSubobjectAffineCoverExt` — `lem-weil-pbc-quasicoherent-subobject-affine-cover-ext`
- `Sheaf.AlgebraicGeometry.RankOneGenericIdealInclusion` — `lem-pc-r2-rank-one-generic-ideal-inclusion`
- `Sheaf.AlgebraicGeometry.RankOneGenericIdealInclusionAux` — `new-rank-one-generic-ideal-inclusion-aux`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme` — `lem-weil-pbc-reduced-induced-closed-subscheme`
- `Sheaf.AlgebraicGeometry.RelativeFlatModuleStalk` — `lem-pc-relative-flat-module-stalk`
- `Sheaf.AlgebraicGeometry.RelativeFlatOfStalks` — `lem-pc-relative-flat-of-stalks`
- `Sheaf.AlgebraicGeometry.RelativeSpecMorphismChart` — `lem-weil-pbc-relative-spec-morphism-chart`
- `Sheaf.AlgebraicGeometry.RelativeSpectrumAffineRealization` — `lem-weil-pbc-relative-spectrum-affine-realization`
- `Sheaf.AlgebraicGeometry.RelativeSpectrumStructureAlgebra` — `lem-weil-pbc-relative-spectrum-structure-algebra`
- `Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback` — `lem-pc-relatively-flat-module-pullback`
- `Sheaf.AlgebraicGeometry.ResolutionOpenComparisonMap` — `def-pc-resolution-open-comparison-map`
- `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionCore` — `lem-pc-resolution-open-restriction-core`
- `Sheaf.AlgebraicGeometry.ResolutionOpenRestrictionNatural` — `lem-pc-resolution-open-restriction-natural`
- `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison` — `lem-pc-resolution-open-scalar-comparison`
- `Sheaf.AlgebraicGeometry.ResolutionOpenScalarCore` — `lem-pc-resolution-open-scalar-core`
- `Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar` — `lem-pc-resolution-sections-homology-scalar`
- `Sheaf.AlgebraicGeometry.ResolutionUnitTwistComparison` — `lem-pc-resolution-unit-twist-comparison`
- `Sheaf.AlgebraicGeometry.RestrictedResolutionSectionsExist` — `lem-pc-restricted-resolution-sections-exist`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` — `def-pc-ringed-spaces-derived-direct-image`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` — `lem-pc-ringed-spaces-derived-direct-image-composition`
- `Sheaf.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic` — `lem-pc-ringed-space-direct-image-kinjective-acyclic`
- `Sheaf.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization` — `lem-pc-ringed-space-kflat-direct-image-hom-localization`
- `Sheaf.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction` — `lem-pc-ringed-space-pasted-pullback-adjunction`
- `Sheaf.AlgebraicGeometry.RingedSpacePastedUnitKFlatHom` — `lem-pc-ringed-space-pasted-unit-kflat-hom`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute` — `lem-pc-ringed-space-tensor-pullback-absolute`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux` — `q3-ringed-space-tensor-pullback-absolute-postcomposition`, `q3-ringed-space-tensor-pullback-left-derived`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived` — `lem-pc-ringed-space-tensor-pullback-underived`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` — `def-pc-derived-direct-image`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives` — `lem-weil-pbc-scheme-modules-enough-injectives`
- `Sheaf.AlgebraicGeometry.SectionBaseChangeZeroPersists` — `lem-pc-section-base-change-zero-persists`
- `Sheaf.AlgebraicGeometry.SectionClearingDenominatorsQCQS` — `lem-sc-p1-section-clearing-denominators-qcqs`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalDenominators` — `lem-pc-section-cohomology-principal-denominators`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` — `lem-pc-section-cohomology-principal-localization`
- `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalTorsion` — `lem-pc-section-cohomology-principal-torsion`
- `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons` — `lem-pc-section-cohomology-unit-comparisons`
- `Sheaf.AlgebraicGeometry.SectionCohomologyUntwistedComparisons` — `lem-pc-section-cohomology-untwisted-comparisons`
- `Sheaf.AlgebraicGeometry.SectionFractionPresentation` — `def-sc-section-fraction-presentation`
- `Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap` — `lem-sc-p1-section-fraction-restriction-map`
- `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus` — `lem-weil-pbc-section-nonvanishing-zero-locus`
- `Sheaf.AlgebraicGeometry.SectionRestrictionSTorsion` — `lem-sc-p1-section-restriction-s-torsion`
- `Sheaf.AlgebraicGeometry.SeparatedOpenInduction` — `lem-sc-invert-s-cohomology-separated-induction`
- `Sheaf.AlgebraicGeometry.SignedCechExtension` — `lem-pc-signed-cech-extension-differential`
- `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism` — `lem-weil-pbc-spec-local-ring-canonical-morphism`
- `Sheaf.AlgebraicGeometry.StalkFromSpecSubopen` — `lem-pc-stalk-from-spec-subopen`
- `Sheaf.AlgebraicGeometry.StalkImageRange` — `lem-weil-pbc-ideal-multiplication-stalk-range-image`
- `Sheaf.AlgebraicGeometry.StalkInternalHomEvaluation` — `lem-weil-pbc-stalk-internal-hom-evaluation`
- `Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation` — `lem-weil-pbc-stalk-internal-hom-finite-presentation`
- `Sheaf.AlgebraicGeometry.StalkLinearMapLocalLiftFinitePresentation` — `lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation`
- `Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso` — `def-pc-stalk-restriction-complex-iso`
- `Sheaf.AlgebraicGeometry.StalkRestrictionSubopenCompatibility` — `lem-pc-stalk-restriction-subopen-compatibility`
- `Sheaf.AlgebraicGeometry.StalkRestrictionWithinIso` — `def-pc-stalk-restriction-within-iso`
- `Sheaf.AlgebraicGeometry.StalkTensorMultiplicationRange` — `lem-weil-pbc-ideal-multiplication-stalk-range-tensor`
- `Sheaf.AlgebraicGeometry.TensorHomRestrictionScalar` — `lem-pc-tensor-hom-restriction-scalar`
- `Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition` — `lem-sc-tensor-power-open-restriction-addition`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` — `lem-sc-tensor-power-section-open-restriction`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN` — `def-sc-tensor-power-open-restriction-comparisons`, `lem-sc-tensor-power-section-open-restriction-N`
- `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT` — `lem-sc-tensor-power-section-open-restriction-T`
- `Sheaf.AlgebraicGeometry.TensorPullback` — `def-pc-module-pullback`, `lem-pc-module-pullback-identity-composition`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` — `lem-pc-module-pullback-adjunction`
- `Sheaf.AlgebraicGeometry.TensorPullbackCompositionAssociativity` — `lem-pc-tensor-pullback-composition-associativity`
- `Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso` — `def-pc-tensor-pullback-composition-iso`
- `Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation` — `lem-pc-tensor-pullback-finite-presentation`
- `Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso` — `lem-pc-tensor-pullback-kflat-quasi-iso`
- `Sheaf.AlgebraicGeometry.TensorUnitPowerScalar` — `lem-pc-tensor-unit-power-scalar`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution` — `lem-weil-pbc-set-cech-nerve-free-resolution`
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly` — `lem-sp-ce-compatible-homotopy-assembly`
- `Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` — `lem-sc-ext-epi-effacement`
- `Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom` — `lem-sc-ext-right-derived-hom`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization` — `lem-weil-pbc-horseshoe-defect-factorization`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap` — `lem-weil-pbc-horseshoe-degreewise-map`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor` — `lem-weil-pbc-horseshoe-delta-functor`
- `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection` — `lem-weil-pbc-horseshoe-homotopy-correction`
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift` — `lem-weil-pbc-horseshoe-correction`, `lem-weil-pbc-horseshoe-morphism-lift`, `lem-weil-pbc-horseshoe-preliminary-data`
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` — `lem-weil-pbc-horseshoe-morphism-lift-exact-source`
- `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions` — `lem-weil-pbc-injective-resolution-ses`
- `Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural` — `lem-sc-acyclic-comparison-natural`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` — `lem-weil-pbc-derived-functor-long-exact`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare` — `lem-sc-injectively-exact-square-resolution-short-exact`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryExact` — `lem-sc-injectively-exact-square-boundary-exact`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryNaturality` — `lem-sc-injectively-exact-square-boundary-naturality`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundarySquareNaturality` — `lem-sc-injectively-exact-square-boundary-square-naturality`
- `Sheaf.CategoryTheory.AbutmentFinitePageComparison` — `lem-sp-abutment-finite-page-comparison`
- `Sheaf.CategoryTheory.AbutmentImageFiltration` — `lem-sp-abutment-image-filtration`
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore` — `lem-sp-bounded-filtered-page-core`
- `Sheaf.CategoryTheory.BoundedFilteredComplexPages` — `thm-sp-spectral-object-yields-canonical-pages`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence` — `thm-sp-spectral-object-yields`
- `Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment` — `lem-sp-bounded-filtered-couple-abutment`
- `Sheaf.CategoryTheory.BoundedFilteredPageConstruction` — `lem-sp-bounded-filtered-page-construction`
- `Sheaf.CategoryTheory.CartanEilenbergAugmentedComparison` — `lem-weil-pbc-ce-augmented-comparison`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonColumnStep` — `lem-weil-pbc-ce-comparison-column-step`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` — `lem-weil-pbc-ce-comparison-cycle-stage`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy` — `lem-sp-cartan-eilenberg-comparison-homotopy`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence` — `lem-sp-cartan-eilenberg-comparison-independence`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage` — `lem-weil-pbc-ce-comparison-object-stage`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows` — `lem-weil-pbc-ce-comparison-augmented-rows`
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy` — `lem-sp-cartan-eilenberg-double-complex-homotopy`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial` — `lem-weil-pbc-cartesian-eilenberg-functorial`
- `Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy` — `lem-sp-ce-vertical-nullhomotopy`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal` — `lem-pur-essential-constant-cofinal-0a1s`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro` — `def-pc-essentially-constant-pro-diagram`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion` — `lem-pur-essential-constant-pro-criterion-05py`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit` — `lem-pc-essentially-constant-pro-hom-colimit`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization` — `lem-pur-left-derived-exact-chosen-localization`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass` — `lem-pur-left-derived-from-kflat-class`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge` — `lem-pur-left-derived-defined-pointwise-kan-bridge`
- `Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy` — `lem-pur-resolving-class-essential-constancy`
- `Sheaf.CategoryTheory.DerivedCoupleBoundaryVanishes` — `lem-sp-derived-couple-boundary-vanishes`
- `Sheaf.CategoryTheory.DerivedCoupleExact` — `lem-sp-derived-couple-exact`, `lem-sp-derived-couple-image-prefix`
- `Sheaf.CategoryTheory.DerivedCoupleKernelIdentities` — `lem-sp-derived-couple-kernel-identities`
- `Sheaf.CategoryTheory.DerivedCoupleMapConstruction` — `lem-sp-derived-map-construction`
- `Sheaf.CategoryTheory.DerivedCoupleMapExactness` — `lem-sp-derived-map-exactness`
- `Sheaf.CategoryTheory.DerivedCoupleMapUniqueness` — `lem-sp-derived-couple-map-uniqueness`
- `Sheaf.CategoryTheory.DerivedFunctorShift` — `lem-pur-derived-functor-shift-05su`
- `Sheaf.CategoryTheory.DerivedFunctorThirdValue` — `lem-pur-derived-functor-triangles-05sc-third-value`
- `Sheaf.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit` — `lem-pur-triangle-retraction-hom-colimit`
- `Sheaf.CategoryTheory.DerivedFunctorTriangles` — `lem-pur-derived-functor-triangles-05sc`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangle` — `lem-pur-derived-functor-triangles-05sc-value-triangle`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompatibility` — `lem-pur-derived-functor-triangles-05sc-value-triangle-compatibility`
- `Sheaf.CategoryTheory.DoubleComplexBoundedBelowTotal` — `lem-weil-pbc-total-bounded-below`
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential` — `lem-weil-pbc-total-first-filtration-differential`
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap` — `lem-weil-pbc-total-first-filtration-map`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorSuccessor` — `lem-weil-pbc-effaceable-delta-functor-successor`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal` — `lem-weil-pbc-effaceable-delta-functor-universal`
- `Sheaf.CategoryTheory.EffacingSequenceComparison` — `lem-weil-pbc-effacing-sequence-comparison`
- `Sheaf.CategoryTheory.EffacingSequencePushout` — `lem-weil-pbc-effacing-sequence-pushout`
- `Sheaf.CategoryTheory.ExactCouple` — source-library module
- `Sheaf.CategoryTheory.ExactCoupleConvergence` — `def-sp-convergence`
- `Sheaf.CategoryTheory.ExactCoupleShifted` — source-library module
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` — `def-weil-extension-by-zero-presheaf`
- `Sheaf.CategoryTheory.FilteredCohomologyDiagonalColimit` — `lem-sp-filtered-cohomology-diagonal-colimit`
- `Sheaf.CategoryTheory.FilteredHomologyCoupleData` — `def-sp-filtered-homology-couple-data`
- `Sheaf.CategoryTheory.FilteredHomologyCoupleExactness` — `lem-sp-filtered-homology-couple-exactness`
- `Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages` — `lem-sp-filtered-homology-couple-quotient-pages`
- `Sheaf.CategoryTheory.FilteredHomologyExactCouple` — `def-sp-filtered-homology-exact-couple`
- `Sheaf.CategoryTheory.FilteredHomologyTowerDifferential` — `lem-sp-filtered-homology-tower-differential`
- `Sheaf.CategoryTheory.FilteredHomologyTowerQuotients` — `lem-sp-filtered-homology-tower-quotients`
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` — `lem-sp-filtered-homotopy-spectral-sequence`, `lem-sp-filtered-homotopy-spectral-sequence-filtered-abutment-map`, `lem-sp-filtered-homotopy-spectral-sequence-page-map`
- `Sheaf.CategoryTheory.FilteredQuotientCanonicalFunctor` — `lem-sp-filtered-quotient-canonical-functor`
- `Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure` — `lem-sp-filtered-quotient-canonical-structure`
- `Sheaf.CategoryTheory.FilteredQuotientFirstConnecting` — `lem-sp-filtered-quotient-first-connecting`
- `Sheaf.CategoryTheory.FilteredQuotientHomologyNaturality` — `lem-sp-filtered-quotient-homology-naturality`
- `Sheaf.CategoryTheory.FilteredQuotientPageRealization` — `lem-sp-filtered-quotient-page-realization`
- `Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps` — `lem-sp-filtered-quotient-successor-cycle-maps`
- `Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel` — `lem-sp-finite-boundary-alpha-kernel`
- `Sheaf.CategoryTheory.FiniteCoconeExactCouple` — `lem-sp-finite-cocone-exact-couple`
- `Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries` — `lem-sp-finite-cocone-limit-boundaries`
- `Sheaf.CategoryTheory.FiniteCoconeLimitCycles` — `lem-sp-finite-cocone-limit-cycles`
- `Sheaf.CategoryTheory.FiniteCoconeLimits` — `lem-sp-finite-cocone-limits`
- `Sheaf.CategoryTheory.FiniteCoconeStationary` — `lem-sp-finite-cocone-stationary`
- `Sheaf.CategoryTheory.FiniteCoconeWeakMaps` — `lem-sp-finite-cocone-weak-maps`
- `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` — `lem-sp-finite-cycle-derived-comparison`
- `Sheaf.CategoryTheory.FiniteCycleFormula` — `lem-sp-finite-cycle-formula`
- `Sheaf.CategoryTheory.FiniteCycleKernelPresentation` — `lem-sp-finite-cycle-kernel-presentation`
- `Sheaf.CategoryTheory.FiniteFiltrationInduction` — `lem-sp-finite-filtration-induction`
- `Sheaf.CategoryTheory.FiniteFiltrationRefinement` — `lem-pc-s3-finite-filtration-refinement`
- `Sheaf.CategoryTheory.FinitePageGradedQuotient` — `lem-sp-finite-page-graded-quotient`
- `Sheaf.CategoryTheory.FinitePageImageLift` — `lem-sp-finite-page-image-lift`
- `Sheaf.CategoryTheory.FinitePageImageQuotient` — `lem-sp-finite-page-image-quotient`
- `Sheaf.CategoryTheory.HalfPlaneConvergence` — `thm-sp-half-plane-convergence`
- `Sheaf.CategoryTheory.HalfPlaneDiagonalColimits` — `lem-sp-half-plane-diagonal-colimits`
- `Sheaf.CategoryTheory.HalfPlaneSharpBounds` — `lem-sp-half-plane-sharp-bounds`
- `Sheaf.CategoryTheory.HalfPlaneWeakConvergence` — `lem-sp-half-plane-weak-convergence`
- `Sheaf.CategoryTheory.HorizontalComparisonLift` — `lem-sp-ce-horizontal-lift`
- `Sheaf.CategoryTheory.InjectiveModulePresheaf` — `lem-weil-pbc-ringed-site-injective-module-injective-presheaf`
- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` — `def-pur-saturated-triangulated-localization`
- `Sheaf.CategoryTheory.LeftDerivedExactWhenDefined` — `lem-pur-left-derived-exact-when-defined`
- `Sheaf.CategoryTheory.LeftDerivedKanSourceTriangles` — `lem-pur-left-derived-kan-source-triangles`
- `Sheaf.CategoryTheory.LeftDerivedKanTriangleValueComparison` — `lem-pur-left-derived-kan-triangle-value-comparison`
- `Sheaf.CategoryTheory.LeftDerivedValueMorphism` — `lem-pur-derived-functor-morphisms-05sa`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact` — `lem-pur-site-restriction-module-adjunction-exact`
- `Sheaf.CategoryTheory.NormalizedGradedFiniteKernel` — `lem-sp-normalized-graded-finite-kernel`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction` — `lem-pc-presheaf-change-of-rings-adjunction`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso` — `lem-weil-pbc-derived-functor-truncation-iso`, `lem-weil-pbc-derived-functor-truncation-iso-epi`, `lem-weil-pbc-derived-functor-truncation-iso-mono`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` — `lem-weil-pbc-right-derived-universal-delta-functor`
- `Sheaf.CategoryTheory.RightKanExtensionCoherentShift` — `lem-pur-right-kan-extension-coherent-shift`
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` — `lem-pur-ringed-site-grothendieck-abelian`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` — `prop-pur-kinjective-resolutions-exist`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit` — `lem-weil-pbc-sheaf-algebras-directed-colimit`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitAlgebraCore` — `stage3-sheaf-algebras-directed-colimit-algebra-core`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitModuleCore` — `stage3-sheaf-algebras-directed-colimit-module-core`
- `Sheaf.CategoryTheory.SiteExtensionByZeroExact` — `lem-weil-pbc-site-extension-by-zero-exact`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf` — `def-weil-pbc-site-extension-by-zero-presheaf`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint` — `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `Sheaf.CategoryTheory.SiteSesCechH1Surjective` — `lem-weil-pbc-site-ses-cech-h1-surjective`
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation` — `new-sheaf-cohomology-derived-evaluation`
- `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections` — `lem-sc-site-cohomology-right-derived-sections`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` — `lem-sc-injective-module-abelian-acyclic-zariski`
- `Sheaf.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic` — `lem-sc-injective-presheaf-module-nerve-acyclic`
- `Sheaf.CategoryTheory.Sites.PresheafCechComplex` — `def-sc-presheaf-cech-complex`
- `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective` — `lem-sc-presheaf-cech-ext-edge-injective`
- `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeKernel` — `lem-sc-presheaf-cech-ext-edge-kernel`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafAugmentationExact` — `lem-sc-presheaf-cech-sheaf-augmentation-exact`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafHomComparison` — `lem-sc-presheaf-cech-sheaf-hom-comparison`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafPositiveExact` — `lem-sc-presheaf-cech-sheaf-positive-exact`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafResolution` — `lem-sc-presheaf-cech-sheaf-resolution`
- `Sheaf.CategoryTheory.Sites.PresheafCechVanishingCriterion` — `lem-sc-presheaf-cech-vanishing-criterion`
- `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` — `lem-sc-presheaf-free-ext-local-killing`, `lem-sc-presheaf-free-ext-local-killing-witness`
- `Sheaf.CategoryTheory.Sites.PresheafFreeNerveComparison` — `lem-sc-presheaf-free-nerve-comparison`
- `Sheaf.CategoryTheory.Sites.PresheafFreeNerveExact` — `lem-sc-presheaf-free-nerve-exact`, `lem-sc-presheaf-free-nerve-exact-eval`, `lem-sc-presheaf-free-nerve-exact-eval-glue`
- `Sheaf.CategoryTheory.SplitCategoryNullHomotopy` — `lem-pc-split-category-null-homotopy`
- `Sheaf.CategoryTheory.SubobjectHomologyStep` — `lem-sp-subobject-homology-step`
- `Sheaf.CategoryTheory.ThirdValueConstruction` — `lem-pur-derived-functor-triangles-05sc-third-value-core`
- `Sheaf.CategoryTheory.TriangleCommonRefinement` — `lem-pur-triangle-common-refinement-ms3-05r9`
- `Sheaf.CategoryTheory.TriangleMorphismCategory` — `lem-pur-triangle-morphism-category-05r9`
- `Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion` — `lem-pur-triangle-completion-ms6-05r9`
- `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension` — `lem-weil-pbc-triangle-morphism-extension`
- `Sheaf.CategoryTheory.TriangulatedHomColimitComparison` — `lem-pur-triangulated-hom-colimit-comparison`
- `Sheaf.CategoryTheory.TruncationAbutmentCocone` — `lem-sp-truncation-abutment-cocone`
- `Sheaf.CategoryTheory.TruncationAbutmentCoconeAux` — `lem-sp-truncation-abutment-cocone-aux`
- `Sheaf.CategoryTheory.TruncationCanonicalAbutment` — `lem-sp-truncation-canonical-abutment`
- `Sheaf.CategoryTheory.TruncationCouple` — `def-sp-truncation-couple`
- `Sheaf.CategoryTheory.TruncationHypercohomology` — `thm-sp-truncation-e2`
- `Sheaf.CategoryTheory.TruncationQuadrantVanishing` — `lem-sp-truncation-quadrant-vanishing`
- `Sheaf.CategoryTheory.TruncationRawExact` — `lem-sp-truncation-raw-exact`
- `Sheaf.CategoryTheory.TruncationTriangle` — `lem-weil-pbc-truncation-triangle`
- `Sheaf.Combinatorics.SignedFacePermutation` — `lem-pc-signed-face-permutation`
- `Sheaf.LinearAlgebra.KernelBasisOfUnitValue` — `lem-weil-pbc-kernel-basis-unit-value`
- `Sheaf.Paper.CohomologyFractionComparison` — `lem-sc-cohomology-fraction-comparison`
- `Sheaf.Paper.CohomologyFractionMayerVietorisExact` — `lem-sc-cohomology-fraction-mayer-vietoris-exact`
- `Sheaf.Paper.CohomologyFractionMayerVietorisSquares` — `lem-sc-cohomology-fraction-mayer-vietoris-squares`
- `Sheaf.Paper.CohomologySectionDivision` — `lem-sc-cohomology-section-division`
- `Sheaf.Paper.DerivedHomMayerVietoris` — `lem-sc-derived-hom-mayer-vietoris`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise` — `lem-weil-pbc-directed-colimit-base-change-elementwise`
- `Sheaf.Paper.FreeComplexBaseLift` — `lem-weil-pbc-free-complex-base-lift`
- `Sheaf.Paper.FreeComplexExtendFamily` — `lem-weil-pbc-free-complex-extend-family`
- `Sheaf.Paper.FreeComplexMapsToResolution` — `lem-weil-pbc-free-complex-maps-to-resolution`
- `Sheaf.Paper.HigherDirectImagePresheaf` — `lem-weil-pbc-higher-direct-image-presheaf`
- `Sheaf.Paper.LocalizedCohomologyMayerVietoris` — `lem-sc-invert-s-cohomology-mayer-vietoris-diagram`
- `Sheaf.Paper.NonvanishingSectionTrivializes` — `lem-weil-pbc-nonvanishing-section-trivializes`
- `Sheaf.Paper.PQFCohomology` — `pqf-def-cohomology`
- `Sheaf.Paper.SiteRestrictionExact` — `lem-weil-pbc-site-restriction-exact`
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree` — `lem-sc-zariski-module-abelian-cohomology-agree`
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` — `lem-sc-module-abelian-zariski-cohomology`, `new-zariski-module-abelian-cohomology-components`
- `Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership` — `lem-sc-affine-finite-projective-prime-membership`
- `Sheaf.RingTheory.BaseChangeDiagramElementwise` — `lem-weil-pbc-base-change-diagram-elementwise`
- `Sheaf.RingTheory.BaseChangeIdealKernelGenerators` — `lem-weil-pbc-base-change-ideal-kernel-generators`
- `Sheaf.RingTheory.CanonicalLocalizedApproximationLimit` — `lem-weil-pbc-canonical-localized-approximation-limit`
- `Sheaf.RingTheory.ColimitEventuallyFlat` — `lem-weil-pbc-colimit-eventually-flat`
- `Sheaf.RingTheory.ColimitFlatRelationDescentElementwise` — `lem-weil-pbc-colimit-flat-relation-descent`, `lem-weil-pbc-colimit-flat-relation-descent-elementwise`
- `Sheaf.RingTheory.ColimitMaximalKernelDescent` — `lem-weil-pbc-colimit-maximal-kernel-descent`
- `Sheaf.RingTheory.ComparisonMapFiniteStage` — `lem-weil-pbc-comparison-map-finite-stage`
- `Sheaf.RingTheory.ComparisonTensorCanonicalCocones` — `lem-weil-pbc-comparison-tensor-canonical-cocones-b4`
- `Sheaf.RingTheory.ComparisonTensorCanonicalMaps` — `lem-weil-pbc-comparison-tensor-canonical-maps-b4`
- `Sheaf.RingTheory.ComparisonTensorCocones` — `lem-weil-pbc-comparison-tensor-cocones-n3`
- `Sheaf.RingTheory.ComparisonTensorDiagrams` — `lem-weil-pbc-comparison-tensor-diagrams-b4`
- `Sheaf.RingTheory.ComparisonTensorLocalSystem` — `lem-weil-pbc-comparison-tensor-local-system-j3`
- `Sheaf.RingTheory.ComparisonTensorNaturalExtension` — `lem-weil-pbc-comparison-tensor-natural-extension-j3`
- `Sheaf.RingTheory.ComparisonTensorStageDiagrams` — `lem-weil-pbc-comparison-tensor-stage-diagrams-j3`
- `Sheaf.RingTheory.ComparisonTensorTransitionPushout` — `lem-weil-pbc-comparison-tensor-transition-pushout-j3`
- `Sheaf.RingTheory.CompatibleModuleModelDescent` — `lem-pc-compatible-module-model-descent`
- `Sheaf.RingTheory.DirectedTensorCoconesColimit` — `lem-weil-pbc-directed-tensor-cocones-colimit-n3`
- `Sheaf.RingTheory.ElementwiseFpModuleEquivDescent` — `lem-pc-elementwise-fp-module-equiv-descent`
- `Sheaf.RingTheory.FilteredPushoutBijectiveStage` — `lem-weil-pbc-filtered-pushout-bijective-stage`
- `Sheaf.RingTheory.FiniteFreeSplitTopCancellation` — `lem-pc-finite-free-split-top-cancellation`
- `Sheaf.RingTheory.FiniteIdealKernelDescent` — `lem-weil-pbc-finite-ideal-kernel-descent`
- `Sheaf.RingTheory.FiniteMapColimitDescent` — `lem-weil-pbc-colimit-finite-ring-map`
- `Sheaf.RingTheory.FinitePresentationModuleBaseChangeDiagram` — `lem-weil-pbc-finite-presentation-base-change-diagram`
- `Sheaf.RingTheory.FinitePresentationModuleDiagram` — `lem-weil-pbc-finite-presentation-module-diagram`
- `Sheaf.RingTheory.FiniteProjectiveComplexFreeModel` — `lem-pc-finite-projective-complex-free-model`
- `Sheaf.RingTheory.FiniteTensorKernelGenerators` — `lem-weil-pbc-finite-tensor-kernel-generators`
- `Sheaf.RingTheory.FiniteTypeApproximationFlatLoci` — `lem-pc-finite-type-approximation-flat-loci`
- `Sheaf.RingTheory.FiniteTypeApproximationFlatPoint` — `lem-pc-finite-type-approximation-flat-point`
- `Sheaf.RingTheory.FiniteTypeApproximationFlatStage` — `lem-pc-finite-type-approximation-flat-stage`
- `Sheaf.RingTheory.Flat.LocalizationPreservesFlatness` — `lem-pc-affine-flat-module-localization-preserves-flatness`
- `Sheaf.RingTheory.FlatLocalizedModuleBaseChange` — `lem-weil-pbc-flat-localized-module-base-change`
- `Sheaf.RingTheory.FlatModuleAtPrime` — `lem-pc-affine-flat-module-local-criterion`
- `Sheaf.RingTheory.FlatModuleTensorModel` — `lem-pc-flat-module-tensor-model`
- `Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` — `lem-weil-pbc-flat-another-variant-local-criterion`
- `Sheaf.RingTheory.FlatPointNoetherianModel` — `lem-weil-pbc-flat-point-noetherian-model`
- `Sheaf.RingTheory.FlatQuotientPresentationIntersection` — `lem-weil-pbc-flat-quotient-presentation-intersection`
- `Sheaf.RingTheory.FlatSemilinearEquiv` — `lem-pc-flat-semilinear-equiv`
- `Sheaf.RingTheory.FpModuleTensorModelComparison` — `lem-pc-fp-module-tensor-model-comparison`
- `Sheaf.RingTheory.FreePrimeMembership` — `lem-sc-free-prime-membership`
- `Sheaf.RingTheory.IntegerApproximationFlatPointStage` — `lem-weil-pbc-integer-approximation-flat-point-stage`
- `Sheaf.RingTheory.IntegralElementsColimitDescent` — `lem-weil-pbc-integral-tensor-generators-colimit-descent`
- `Sheaf.RingTheory.LimitModuleFinitePresentation` — `lem-weil-pbc-limit-module-finite-presentation`
- `Sheaf.RingTheory.LocalizationIdealKernelGenerators` — `lem-weil-pbc-localization-ideal-kernel-generators`
- `Sheaf.RingTheory.LocalizedApproximationBaseChange` — `lem-pc-localized-approximation-base-change`
- `Sheaf.RingTheory.LocalizedApproximationCocones` — `lem-weil-pbc-localized-approximation-cocones`
- `Sheaf.RingTheory.LocalizedApproximationColimits` — `lem-pc-localized-approximation-colimits`
- `Sheaf.RingTheory.LocalizedApproximationTransitions` — `lem-weil-pbc-localized-approximation-transitions`
- `Sheaf.RingTheory.LocalizedBaseChangeIdealKernelSpan` — `lem-weil-pbc-localized-base-change-ideal-kernel-span`
- `Sheaf.RingTheory.LocalizedBaseChangeQuotientFlat` — `lem-weil-pbc-localized-base-change-quotient-flat`
- `Sheaf.RingTheory.LocalizedModuleColimitComparison` — `lem-pc-localized-module-colimit-comparison`
- `Sheaf.RingTheory.LocalizedRingColimitComparison` — `lem-pc-localized-ring-colimit-comparison`
- `Sheaf.RingTheory.ModuleBaseChangeAcrossPushout` — `lem-weil-pbc-module-base-change-across-pushout`
- `Sheaf.RingTheory.NoetherianApproximationLocalizedDiagrams` — `lem-weil-pbc-noetherian-approximation-localized-diagrams`
- `Sheaf.RingTheory.OpenFlatLocus` — `lem-weil-pbc-openness-of-flatness`
- `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel` — `lem-pc-pseudo-coherent-bounded-finite-free-model`
- `Sheaf.RingTheory.RingPseudoCoherent` — `def-pc-ring-pseudo-coherent-complex`
- `Sheaf.RingTheory.TensorAlgebraStructureFiniteStage` — `lem-weil-pbc-tensor-algebra-structure-finite-stage`
- `Sheaf.RingTheory.TensorCyclesFlatCokernel` — `lem-weil-pbc-tensor-cycles-flat-cokernel`
- `Sheaf.RingTheory.TensorModelAlgebraDescent` — `lem-pc-tensor-model-algebra-descent`
- `Sheaf.RingTheory.TensorModelAlgebraStage` — `lem-pc-tensor-model-algebra-stage`
- `Sheaf.RingTheory.TensorModelComparisonDiagram` — `lem-pc-tensor-model-comparison-diagram`
- `Sheaf.RingTheory.TensorModelPushoutBaseChange` — `lem-pc-tensor-model-pushout-base-change`
- `Sheaf.RingTheory.TensorRightFactorFiniteStage` — `lem-weil-pbc-tensor-right-factor-finite-stage`
- `Sheaf.RingTheory.TensorTailColimitElementwise` — `lem-pc-tensor-tail-colimit-elementwise`
- `Sheaf.RingTheory.TorIdealComparisonCompatibility` — `lem-weil-pbc-tor-ideal-comparison-compatibility`
- `Sheaf.RingTheory.TorIdealConnectingFormula` — `lem-weil-pbc-tor-ideal-connecting-formula`
- `Sheaf.RingTheory.TorIdealCycleLift` — `lem-weil-pbc-quotient-cycle-lift`
- `Sheaf.RingTheory.TorIdealHomologyExactness` — `lem-weil-pbc-tor-ideal-homology-exactness`
- `Sheaf.RingTheory.TorIdealHomologyFormula` — `lem-weil-pbc-tor-ideal-homology-formula`
- `Sheaf.RingTheory.TorIdealKernelNaturality` — `lem-weil-pbc-tor-ideal-kernel-naturality`
- `Sheaf.RingTheory.TorIdealQuotientChainMap` — `lem-weil-pbc-quotient-tensor-comparison`
- `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle` — `lem-weil-pbc-tor-one-second-additive`, `lem-weil-pbc-tor-one-second-linear`, `lem-weil-pbc-tor-one-surjective-flat-middle`
- `Sheaf.Topology.FiniteTypeLocalCoefficients` — `lem-weil-pbc-finite-type-local-coefficients`
- `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` — `lem-weil-pbc-module-finite-type-surjective-on-stalk`
- `Sheaf.Topology.GlueSheavesOfModules` — `lem-weil-pbc-glue-sheaves-of-modules`
- `Sheaf.Topology.InverseImageModule` — `def-pc-topological-inverse-image-module`
- `Sheaf.Topology.InverseImageOperationExt` — `lem-pc-inverse-image-operation-ext`
- `Sheaf.Topology.InverseImagePresheafModule` — `lem-pc-inverse-image-presheaf-module`
- `Sheaf.Topology.InverseImageStalk` — `lem-weil-pbc-topological-inverse-image-stalk`
- `Sheaf.Topology.ModuleCohomologyTopComparison` — `lem-weil-pbc-module-cohomology-top-comparison`
- `Sheaf.Topology.ModuleCompatibleFamilyPresheaf` — `def-weil-pbc-module-compatible-family-presheaf`
- `Sheaf.Topology.ModuleCompatibleFamilySheaf` — `lem-weil-pbc-module-compatible-family-sheaf`
- `Sheaf.Topology.ModuleCompatibleFamilySheafCondition` — `lem-weil-pbc-module-compatible-family-sheaf-condition`
- `Sheaf.Topology.ModuleCompatibleFamilySmall` — `lem-weil-pbc-module-compatible-family-small`
- `Sheaf.Topology.ModuleMayerVietoris` — `lem-sc-mayer-vietoris-ringed-space`
- `Sheaf.Topology.ModuleObjectOpenDescent` — `lem-weil-pbc-module-object-open-descent`, `lem-weil-pbc-module-object-open-descent-diagonal`
- `Sheaf.Topology.ModuleObjectOpenDescentAux` — `lem-weil-pbc-module-object-open-descent-aux-diagonal`
- `Sheaf.Topology.OpenModuleCohomology` — `def-sc-open-module-cohomology`
- `Sheaf.Topology.OpenModuleCohomologyLocalIso` — `lem-sc-open-module-cohomology-local-iso`
- `Sheaf.Topology.PresheafModuleStalkFunctor` — `def-weil-pbc-module-stalk`
- `Sheaf.Topology.PresheafStalkTensor` — `lem-pc-presheaf-module-stalk-tensor`
- `Sheaf.Topology.RestrictInjectiveResolution` — `lem-sc-ringed-space-restrict-injective-resolution`
- `Sheaf.Topology.RingedModuleSkyscraper` — `def-pc-ringed-module-skyscraper`
- `Sheaf.Topology.RingedSpaceModuleCohomology` — `def-sc-ringed-space-module-cohomology`, `def-sc-sheaf-cohomology-functor`
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives` — `lem-sc-ringed-space-module-sheaves-enough-injectives`
- `Sheaf.Topology.SheafCokernelLocalImage` — `lem-weil-pbc-sheaf-cokernel-local-image`
- `Sheaf.Topology.SkyscraperComplex` — `lem-pc-skyscraper-complex`
- `Sheaf.Topology.SkyscraperComplexAcyclic` — `lem-pc-skyscraper-complex-acyclic`
- `Sheaf.Topology.SkyscraperComplexStalk` — `lem-pc-skyscraper-complex-stalk-recovery`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.Bidual` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` — `def-pur-sheaf-hom`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` — `lem-weil-pbc-module-tensor-symmetric-monoidal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` — source-library module
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` — source-library module
- `WeilConjectures.Algebra.Homology.BifunctorLinear` — source-library module
- `WeilConjectures.Algebra.Homology.ExactCouple.Basic` — `def-sp-exact-couple`
- `WeilConjectures.Algebra.Homology.FlatComplex` — source-library module
- `WeilConjectures.Algebra.Homology.FlatComplexBaseChange` — source-library module
- `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided` — source-library module
- `WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure` — source-library module
- `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom` — source-library module
- `WeilConjectures.Algebra.Homology.InternalHom` — source-library module
- `WeilConjectures.Algebra.Homology.Monoidal.Dual` — source-library module
- `WeilConjectures.Algebra.Homology.SplitSubmodulesStable` — `lem-weil-pbc-split-submodules-stable`
- `WeilConjectures.AlgebraicGeometry.Ample` — `def-weil-pbc-ample-invertible-module`
- `WeilConjectures.AlgebraicGeometry.ChowLemma` — `cor-chow-lemma-proper`, `lem-weil-pbc-chow-noetherian`, `thm-chow-lemma`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel` — `lem-chow-closed-model`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.Glue` — `lem-chow-glue`, `lem-chow-preimage`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.Graph` — `lem-chow-graph`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.Reduction` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism` — `lem-pc-closed-immersion-coherent-cohomology`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech` — `lem-pc-affine-cech-complex`, `lem-pc-affine-vanishing`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` — `lem-pc-cech-computes`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` — `def-pc-euler-characteristic`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism` — `lem-pc-affine-morphism-hi`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` — `def-pc-scheme-module-flat-over`, `lem-pc-scheme-modules-grothendieck-abelian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechFlat` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModule` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Field` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` — `def-pc-invertible-in-degree-zero`, `lem-pc-coherent-hi`, `lem-pc-universal-finite-free-complex`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.ProjectionFormula` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` — `lem-pc-cohomology-sections-affine-base`, `lem-pc-higher-direct-image-local-vanishing`, `lem-pc-projection-formula`, `lem-pc-sections-higher-direct-image-quasi-coherent`, `lem-pc-sections-open-base-change`, `new-higher-direct-image-affine-local-qcoherent`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Exact` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Flasque` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.Leray` — source-library module
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact` — `lem-pc-euler-additive`
- `WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero` — source-library module
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf` — `def-weil-pbc-comm-algebra-sheaf`
- `WeilConjectures.AlgebraicGeometry.Descent` — `lem-pc-descent-finite-flat-closed-subschemes`, `lem-pc-fpqc-descent`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier` — `def-pc-divisor-line-bundle`, `lem-pc-cartier-affine-generator-regular`, `lem-pc-divisor-line-bundle-flat-pullback`, `lem-pc-divisor-line-bundle-invertible`, `lem-pc-divisor-line-bundle-properties`, `lem-pc-recd-pullback`
- `WeilConjectures.AlgebraicGeometry.Modules.AffineComplement` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.AffineDescent` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` — `lem-pc-section-clearing-denominators`
- `WeilConjectures.AlgebraicGeometry.Modules.DescentEffective` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.DescentGlue` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.Dual` — `lem-pc-tensor-dual-invertible`, `lem-sc-invertible-dual`
- `WeilConjectures.AlgebraicGeometry.Modules.Endomorphism` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent` — `lem-weil-pbc-finite-presentation-affine-sections`
- `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` — `lem-sc-flat-cover-module-isomorphism-reflection`
- `WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.FpqcSections` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.FreeComplex` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` — `def-sc-local-free-generator`
- `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus` — `def-sc-section-generating-locus`
- `WeilConjectures.AlgebraicGeometry.Modules.HomSection` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic` — `lem-sc-ext-evaluation-first-naturality`
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Presheaf` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` — `def-sc-invertible-module`, `lem-weil-pbc-invertible-pullback-invertible`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections` — `lem-sc-affine-invertible-sections`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine` — `lem-pc-affine-sections-finite-locally-free-criterion`, `lem-pc-finite-flat-affine-sections-projective`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` — `lem-pc-invertible-sheaf-instance`, `lem-sc-pullback-tensor-power-iso`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator` — `lem-sc-module-hom-local-bijective-iso`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal` — `lem-pc-adjoint-module-pullback-monoidal`, `lem-pc-scheme-pullback-monoidal-existing`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackSections` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` — `lem-weil-pbc-pushforward-spec-global-sections`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.QcqsSections` — `pqf-lem-qcoh-compact-section-power-torsion`, `pqf-lem-qcoh-qcqs-section-power-extension`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` — `lem-pc-cokernel-finite-presentation-noetherian`, `lem-weil-pbc-quasi-coherent-module-cokernel-closure`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` — `lem-pc-quasicoherent-module-coproducts`, `lem-pqf-kernel-finite-presentation-noetherian`, `lem-weil-pbc-module-restriction-open-immersion-limits`, `lem-weil-pbc-quasi-coherent-module-coproduct-closure`, `lem-weil-pbc-quasi-coherent-module-kernel`, `lem-weil-pbc-quasicoherent-epi-affine-cover`, `pqf-lem-qcoh-principal-open-criterion`
- `WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.StalkExact` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent` — source-library module
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` — `def-pc-zero-scheme`, `lem-pc-invertible-common-free-generator`, `lem-pc-zero-scheme-divisor-iso`, `lem-pc-zero-scheme-ideal-local`, `lem-pc-zero-scheme-pullback-full-local-coefficient`, `lem-pc-zero-scheme-zero-iff`, `lem-sc-canonical-section-zero-scheme`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` — `def-kun-projective`, `def-pc-projective-morphism`
- `WeilConjectures.AlgebraicGeometry.Picard.Defs` — `def-pc-pic-sigma-functor`, `def-pc-picard-functor`, `lem-pc-k-sheaf`, `lem-pc-pic-exact`, `lem-pd-picard-base-change`, `thm-pc-pic-split`
- `WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent` — source-library module
- `WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.Basic` — source-library module
- `WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.DescentData` — source-library module
- `WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.DescentDataModules` — source-library module
- `WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.Modules` — source-library module
- `WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent` — source-library module
- `WeilConjectures.AlgebraicGeometry.PicardFunctor` — `def-pc-picard-presheaf`, `def-sc-picard-group`, `lem-pc-pic-presheaf-functorial`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` — `def-nagata-projective-space-base-change`, `lem-pc-projective-proper`, `lemma-nagata-projective-space-base-change-proper`, `lemma-nagata-projective-space-base-change-pullback`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion` — `lem-chow-affine-immersion`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection` — `def-pc-linear-pair-morphism`, `lem-pc-linear-pair-morphism-finite`, `lem-pc-linear-pair-morphism-gluing`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech` — `lem-pc-projective-space-serre-pairing`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product` — `lem-chow-segre`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre` — `def-chow-segre`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` — `def-pc-projective-space-twist`, `lem-pc-twist-tensor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero` — `lem-weil-pbc-projective-space-zero-isomorphism`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules` — `def-weil-pbc-proj-twisting-sheaf`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Mul` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sheaf` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj` — source-library module
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist` — source-library module
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections` — source-library module
- `WeilConjectures.CategoryTheory.Abelian.DimensionShifting` — source-library module
- `WeilConjectures.CategoryTheory.Abelian.Flat.Basic` — `lem-weil-pbc-flat-coproduct`
- `WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat` — source-library module
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp` — source-library module
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting` — source-library module
- `WeilConjectures.CategoryTheory.CommAlgebraSheafModule` — `def-weil-pbc-ringed-space-algebra-module`
- `WeilConjectures.CategoryTheory.DeltaFunctor` — `def-weil-pbc-delta-functor`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` — `lem-kun-flat-bounded-tor-amplitude`, `lem-pc-source-kflat-module-tensor-model`, `lem-pc-source-module-kflat-resolution`, `lem-sc-source-tor-amplitude-flat-model`, `lem-sc-source-tor-amplitude-lower-tensor-bound`, `lem-sc-source-tor-amplitude-upper-tensor-bound`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` — `lem-sc-source-kflat-tensor-left-triangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` — `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` — source-library module
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility` — `src-right-derived-functor-plus-compatibility`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` — `lem-pc-right-derived-functor-triangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` — `lem-pc-derived-category-locally-small`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective` — `lem-pur-kinjective-degreewise-existence`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` — `lem-weil-pbc-sheaf-flat-separator`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits` — source-library module
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` — `lem-weil-pbc-sheaf-tensor-closed`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` — `lem-weil-pbc-termwise-adjunction-homotopy`
- `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` — source-library module
- `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided` — source-library module
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` — source-library module
- `WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory` — source-library module
- `WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat` — source-library module
- `WeilConjectures.CategoryTheory.SiteCechComplex` — `def-weil-pbc-site-cech-complex`
- `WeilConjectures.CategoryTheory.Sites.CechComplexFunctor` — source-library module
- `WeilConjectures.CategoryTheory.Sites.SigmaPresheaf` — source-library module
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlus` — source-library module
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf` — source-library module
- `WeilConjectures.CategoryTheory.SpectralSequence.LowDegree` — source-library module
- `WeilConjectures.Compactification.FiniteTypeExtension` — `def-nagata-finite-type-ideal-extension`, `lemma-nagata-extend-finite-type-ideal`, `lemma-nagata-finite-type-ideal-extension-exists`
- `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone` — `lem-pc-tensor-mapping-cone-iso`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Pretriangulated` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.ShiftSequence` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Monoidal` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.ObjectProperty` — source-library module
- `WeilConjectures.FromJoel.Algebra.Homology.Single` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerived` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedFour` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedThree` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Limits.Constructions.EventuallyConstant` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.Composition` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesFour` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesThree` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Monoidal` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Product` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` — `def-pc-module-kflat-complex`, `lem-kun-derived-tensor-well-defined`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Pentagon` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.QuotientThree` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.QuotientTwo` — source-library module
- `WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.AlgCat.FilteredColimits` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.Grp.Preadditive` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` — `lem-weil-pbc-ring-sheaves-grothendieck`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` — `def-amb-finite-locally-free-module`, `def-sc-finite-locally-free-sheaf`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Basic` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions` — source-library module
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits` — `lem-weil-pbc-directed-subalgebra-ring-colimit`, `lemma-nagata-ring-finite-type-subalgebras`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation` — `lem-kun-fp-algebra-descent`
- `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` — `lem-pc-total-bifunctor-comparison-iso`
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.Localization` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Ab` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat` — source-library module
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` — `thm-sp-double-complex-spectral-sequences`
- `WeilConjectures.Mathlib.Algebra.Module.LocalizedModule.Exact` — source-library module
- `WeilConjectures.Mathlib.Algebra.MvPolynomial.Basic` — source-library module
- `WeilConjectures.Mathlib.Algebra.Polynomial.Laurent` — source-library module
- `WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` — `def-zl-localized-coordinates`, `lemma-nagata-quasi-affine-immersion-affine-space-exists`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` — `def-nagata-basechanged-system`, `def-nagata-closed-subscheme-fp-system`, `def-nagata-finite-type-fp-model-system`, `def-nagata-noetherian-inverse-system`, `lem-weil-pbc-scheme-over-limit`, `lemma-nagata-closed-immersion-stage-exists`, `lemma-nagata-closed-subscheme-fp-system`, `lemma-nagata-finite-presentation-descends`, `lemma-nagata-finite-type-fp-model-system`, `lemma-nagata-fixed-base-separated-eventually`, `lemma-nagata-fixed-base-separated-stage-exists`, `lemma-nagata-immersion-into-fp-model`, `lemma-nagata-noetherian-inverse-system-affine`, `lemma-nagata-separated-descent-stage-exists`, `lemma-nagata-separated-eventually`, `lemma-nagata-separated-stage-exists-absolute`, `pqf-lem-limit-immersion-descends`, `prop-nagata-finite-type-closed-in-fp`, `prop-nagata-noetherian-inverse-system`, `sbc-lem-bc-minimal-counterexample`, `thm-pd-spreading-out`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Cover.Open` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction` — `def-weil-pbc-stein-factorization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Gluing` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine` — `lem-pc-ideal-sheaf-comap-affine-extension`, `lemma-nagata-extended-ideal-affine-chart`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic` — `lemma-nagata-ideal-unit-off-support`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` — `def-nagata-effective-cartier-ideal`, `def-nagata-invertible-ideal`, `lem-pc-flat-pullback-effective-cartier-ideal`, `lem-pc-nonzero-locally-principal-ideal-invertible`, `lemma-nagata-invertible-ideal-tensor-power`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` — `lem-chow-scheme-theoretic-closure`, `lem-sc-mult-n-dim-one-closed-subscheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Limits` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Presheaf` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` — `lem-weil-pbc-module-restriction-iso-stalk-bijective`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` — `lem-weil-pbc-affine-module-basic-open-localization`, `lem-weil-pbc-module-pullback-quasi-coherent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` — `lemma-nagata-scheme-image-universal`, `lemma-nagata-scheme-theoretic-closure-minimal`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` — `lemma-nagata-diagonal-finite-presentation`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` — `lem-kun-dimension-finite-type`, `lem-sc-integral-locally-algebraic-affine-opens-dimension`, `lem-sc-integral-locally-algebraic-opens-dimension`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat` — `lem-pc-flat-source-descent`, `lem-sbc-canonical-stalk-spectrum-flat`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` — `lem-sbc-finite-morphism-fpqc-descent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion` — `lem-chow-tuple-immersion`, `lemma-nagata-immersion-shrink-to-closed`, `lemma-nagata-immersion-shrink-to-closed-exists`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper` — `lem-sc-proper-affine-finite`, `lem-weil-pbc-scheme-theoretic-image-proper`, `pqf-lem-image-proper`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` — `lem-chow-agree-on-dense-open`, `lemma-nagata-dense-flat-pullback`, `lemma-nagata-scheme-image-restrict-open`, `lemma-nagata-valuation-factor-closed`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated` — `lem-weil-pbc-separated-separating-pair-cover`, `lemma-nagata-diagonal-mixed-open`, `lemma-nagata-ext-scheme-theoretically-dominant-separated`, `lemma-nagata-separated-two-open-cover`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Properties` — `lem-chow-affine-through-generic-points`, `lem-chow-disjoint-affines`, `lemma-nagata-conrad-case3-smaller-base`, `lemma-nagata-dense-affine-cover-exists`
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier` — `lem-weil-pbc-surjective-nonempty-fibres`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks` — `lemma-nagata-scheme-image-partial-section`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` — source-library module
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme` — `lem-pc-scheme-connected-iff-idempotents`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` — `lem-galois-fpqc-family-descent-of-local-property`, `lem-weil-pbc-fpqc-family-descent-of-single-morphism-descent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.EssentialImage` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Kernels` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Composition` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Shift.Localization` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.DescentData` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.Precoverage` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` — `lem-galois-flasque`, `lem-weil-pbc-sheaf-ext-cohomology-long-exact`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Skeletal` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` — source-library module
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` — `lem-weil-pbc-commshift-nattrans-triangle-morphism`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated` — source-library module
- `WeilConjectures.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` — source-library module
- `WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank` — source-library module
- `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Associator` — source-library module
- `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Adjoin.FG` — `lem-kun-algebra-union`
- `WeilConjectures.Mathlib.RingTheory.Filtration` — `lem-weil-pbc-flat-variant-local-criterion`
- `WeilConjectures.Mathlib.RingTheory.FinitePresentation` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Flat.Basic` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer` — `lem-weil-pbc-flat-ses-kernel-flat`
- `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` — `lem-weil-pbc-flat-algebra-faithfully-flat-descent`
- `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Descent` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Flat.Localization` — `lem-weil-pbc-noetherian-flat-locus-neighborhood`
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization` — `lemma-nagata-proj-chart-ring-cocycle`
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp` — `lem-weil-pbc-integral-injective-dimension-equal`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Maps` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Ideal.Operations` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.Operations` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal` — source-library module
- `WeilConjectures.Mathlib.RingTheory.IsTensorProduct` — source-library module
- `WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial` — `lem-weil-pbc-mv-polynomial-maximal-height`
- `WeilConjectures.Mathlib.RingTheory.KrullDimension.Zero` — source-library module
- `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic` — `lem-weil-pbc-local-ring-idempotent-zero-one`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Localization.Away.Lemmas` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Localization.Finiteness` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Localization.Ideal` — source-library module
- `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous` — `lem-weil-pbc-dehomogenization-polynomial-ring`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization` — `lem-zl-noether-normalization-dimension`, `lem-zl-spread-normalization`
- `WeilConjectures.Mathlib.RingTheory.PicardGroup` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian` — source-library module
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology` — `lem-wf-affine-dimension-drop`
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.Basic` — source-library module
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG` — source-library module
- `WeilConjectures.Mathlib.Topology.Category.TopCat.Opens` — source-library module
- `WeilConjectures.Mathlib.Topology.Connected.Clopen` — source-library module
- `WeilConjectures.Mathlib.Topology.KrullDimension` — `def-kun-dimension`, `def-kun-topological-dimension-at-point`, `lem-sc-dim-one-point-outside-open-closed`, `lem-sc-dim0-finite`, `lem-sc-nonempty-open-complement-finite-dim-le-one`, `lem-sc-zero-dim-noetherian-closed-finite`, `lem-weil-pbc-dimension-at-point-open-subspace`, `lem-weil-pbc-dimension-bound-open-cover`
- `WeilConjectures.Mathlib.Topology.NoetherianSpace` — source-library module
- `WeilConjectures.Mathlib.Topology.Sheaves.Flasque` — source-library module
- `WeilConjectures.Mathlib.Topology.Sheaves.Presheaf` — source-library module
- `WeilConjectures.Mathlib.Topology.Sober` — source-library module
- `WeilConjectures.RingTheory.FaithfullyFlat.FamilyDescent` — source-library module
- `WeilConjectures.RingTheory.Flat.ShortExact` — source-library module
- `WeilConjectures.RingTheory.GradedAlgebra.Standard` — `def-pc-standard-graded-algebra`, `lem-pc-linear-pair-graded-finite`
- `WeilConjectures.RingTheory.ProEtale.FaithfullyFlat` — `lem-weil-pbc-flat-colimit-presentation-same-universe`, `lem-weil-pbc-flat-ring-map-iff-ind-flat`
- `WeilConjectures.RingTheory.ProEtale.Ind` — source-library module
- `WeilConjectures.Topology.Sheaves.Cech` — `lem-pc-topological-injective-cech-positive-exact`
- `WeilConjectures.Topology.Sheaves.CechCohomology` — `lem-pc-topological-cech-zero-gluing-iso`
- `WeilConjectures.Topology.Sheaves.CechComparison` — source-library module
- `WeilConjectures.Topology.Sheaves.CechCriterion` — `lem-pc-topological-ses-cech-sections-surjective`
- `WeilConjectures.Topology.Sheaves.CechFlasque` — source-library module
- `WeilConjectures.Topology.Sheaves.MayerVietorisVanishing` — source-library module
- `WeilConjectures.Topology.Sheaves.PushforwardCohomology` — `lem-sc-topological-pushforward-injective`

</details>

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated three private helpers that the library already proves
in `FilteredQuotientPageMaps`. They are usable through a proof-only `import all`;
re-proving them locally was unnecessary. The repair removes all three duplicates.

The new decalage statement was checked on the zero filtration, the constant top filtration,
and complexes with zero differential: its formula gives respectively zero, top, and the
shifted original steps. These cases require no boundedness assumptions.

The old Z/B-description theorem assumes one global `F.IsFinite` bound. A CE second filtration
is finite in each total degree, while an unbounded injective resolution has no global
filtration bound. Applying that theorem directly would add an unjustified hypothesis. The
new quotient functor and model use no finiteness bound.

Objectwise quotient descriptions alone do not supply the required normalized successor
isomorphisms or a functor on all filtered complexes. The new canonical sequence supplies
these explicitly, and the model's quotient-image differential and naturality equations are
proved on representatives. An arbitrary `FilteredPageTwoModel` is not asserted to have the
canonical successor normalization; the remaining comparison is deliberately about the
explicit normalized model.

The naturality of total summands already proves filtered preservation. The old homotopy and
convergence dependencies add work that this existence-of-lifts step does not need. No existing
statement is marked disputed. The parent unit and the CE/decalage/truncation route are retained.

## New nodes

- `lem-sp-filtered-complex-canonical-sequence`: the proved normalized quotient-sequence functor;
  attached to `filteredComplexCanonicalPageTwoFunctor`.
- `lem-sp-filtered-complex-canonical-model`: the proved quotient-image model with all its axioms;
  attached to `filteredComplexCanonicalModel`.
- `lem-sp-ce-filtered-total-lifts`: the proved second filtrations and filtered comparison lifts;
  attached to `cartanEilenberg_filtered_total_lifts`.
- `lem-sp-filtered-complex-decalage`: the proved unique functorial decalage filtration;
  attached to `DecreasingFiltration.exists_decalage`.
- `lem-sp-left-exact-truncation-iso`: the proved unique truncation comparison for left exact
  functors; attached to `leftExact_truncation_iso`.
- `lem-sp-ce-truncation-resolution`: the proved unique, functorial injective resolutions of
  upper smart truncations; attached to `cartanEilenberg_truncation_resolution`.
- `lem-sp-ce-derived-truncation-cohomology`: the proved objectwise computation of RG of upper
  truncations by mapped CE totals; attached to `cartanEilenberg_derived_truncation_cohomology`.
- `lem-sp-ce-canonical-truncation-comparison`: the single remaining strict comparison component;
  attached to `cartanEilenberg_canonical_truncation_comparison`.

All new nodes belong to the parent's chapter and unit, carry the source and complete proof
plan, and record searches and their Lean attachment. There are no change records: every
existing signature and public import is preserved, and no forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

1. **Interface and accidental changes.** I compared the delivered item module with the repository version. The existing target declaration and its elaborated statement are unchanged; the proof-only import changes are recorded above. The eight additional modules are new modules attached to new DAG nodes, and no existing declaration was modified.

2. **Compilation and proof validity.** I compiled all sandbox modules with `lcompile.py --all`, then compiled the item module separately; both completed without errors. The only remaining `sorry` is the named theorem `CategoryTheory.cartanEilenberg_canonical_truncation_comparison`, and it has its own node, source, and proof plan. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was introduced.

3. **Statements and new nodes.** I read each new public declaration and its corresponding node. The construction nodes state the concrete quotient sequence/model, filtered lifts, decalage, truncation isomorphism, truncation resolution, and derived cohomology calculation used by the item. The remaining comparison node is strictly smaller than the original target: it fixes the canonical model and asks only for objectwise comparison and page-two naturality, with no external sequence functor or arbitrary witness.

4. **Route and pruning.** The proof follows the unit route through the canonical quotient model, filtered total lifts, and the canonical CE/truncation comparison, then uses page-two extensionality. The removed imports and attached no-longer-needed dependencies are listed above; the old global-filtration Z/B theorem and comparison-independence route are not needed for this construction.

5. **Verdict.** The delivered proof proves the original target statement unchanged and leaves one explicitly named, properly split comparison theorem. The unit's realized route is retained. I changed only this report section during second reading.

## Second reading by J4

1. **Interface and accidental changes.** I compared the delivered item module against the
   repository copy. The public theorem statement is byte-for-byte unchanged. The item adds
   only proof-only imports for the filtered lifts and canonical comparison, plus a private
   extensionality helper. The eight additional modules and their DAG nodes are new delivery
   files; no existing declaration was adapted and no change record is required. Verdict: pass.

2. **Compilation and proof validity.** The delivery dry run compiled every sandbox module
   in dependency order through `lcompile.py` and passed. A separate scratch axiom audit also
   compiled successfully. An initial standalone item compile ran before its dependency
   compilation completed and reported a missing object; the ordered compilation resolved it. The only remaining `sorry`
   is `CategoryTheory.cartanEilenberg_canonical_truncation_comparison`, exactly the named split
   theorem and node `lem-sp-ce-canonical-truncation-comparison`. I found no `axiom`, `unsafe`,
   `opaque`, `extern`, `implemented_by`, or hollow definition. Verdict: pass.

3. **Statements and new nodes.** I read every new public declaration and matched it to its
   node. The canonical quotient sequence/model, filtered CE lifts, decalage, left-exact
   truncation comparison, truncation resolution, and derived truncation cohomology statements
   are concrete and strictly support the item proof. The remaining canonical comparison is a
   strict reduction: it fixes the model and asks only for its comparison and page-two square.
   Edge cases: zero, constant-top, and zero-differential filtrations have the expected
   decalage formula; negative truncation q gives the zero horizontal CE truncation;
   p < 0 or q < 0 yields zero page-two objects on both sides of the remaining comparison
   by the first-quadrant support and right-derived lower bounds. Verdict: pass.

4. **Route and pruning.** The implemented route follows the parent construction through CE
   totals, decalage, truncation, and page-two comparison. The original module no longer imports
   the global finite-filtration Z/B
   theorem or comparison-independence module; the proof directly uses the canonical model and
   filtered total lifts. The report's no-longer-needed closure list records the removed imports
   and dependent nodes. Verdict: pass.

5. **Nodes and unit route.** The original node's proof, proof dependencies, and proof origin
   match the Lean proof. Every split node has source, proof plan, searches, Lean attachment,
   chapter, and unit metadata. The inherited unit `sk-prop-av-pqf-finite` has empty
   `realized.statement` and `realized.steps[0]` arrays; neither is changed or bypassed.
   This item is not the key realization of that proper/quasi-finite unit. Verdict: pass.

Changes made during this reading:

- Added this fresh review record and accounted for every removed parent proof dependency.
- Corrected the derived-cohomology source from Tag 0130 (double-complex spectral-sequence
  pages) to [Tag 0156, Lemma 13.20.1](https://stacks.math.columbia.edu/tag/0156) (computation
  by bounded-below injectives), in the new module's documentation and its node.
- Verified the two canonical construction nodes' Lean signatures in preflight's
  normalized format, which omits declaration modifiers such as `noncomputable`.
  Their original metadata was correct and is retained. No Lean declaration, proof, or
  signature changed.

The explicit axiom audit in `scratchpad/second-reading-axioms.log` covers the new data choices,
seven construction components, remaining comparison, and parent theorem. The constructions
use only `propext`, `Classical.choice`, and `Quot.sound`; the comparison and parent additionally
use `sorryAx`, exactly as expected from the sole remaining named hole. The existing
[Tag 015X](https://stacks.math.columbia.edu/tag/015X) source supports the CE/truncation route.
I applied the [Lean review skill](/home/ubuntu/.codex/skills/lean4/SKILL.md) for this audit.

The required dry run passed: `OK (dry run): commit 8bb1986f95 compiles and passes the preflight;
nothing pushed`. The delivery is classified CODEX because it adds eight modules and nodes and
leaves the single declared comparison hole.

A delivery attempt caught an incorrect metadata-only modifier edit made during review:
preflight compares normalized signatures beginning with `def`, excluding `noncomputable`.
I restored the two original node signature fields and reran the required checks.

Final dry run after restoring the signature metadata: `OK (dry run): commit 2c3692d774
compiles and passes the preflight; nothing pushed`. No proof changes were needed.
