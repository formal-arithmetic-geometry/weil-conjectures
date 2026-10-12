## What changed

Replaced the sole sorry in `Sheaf.Topology.TopologicalLeraySpectralObjectAugmentation`
with a complete Lean reduction from two independent resolution-comparison statements.
The existing declaration and all public imports/signatures/visibility remain identical.
The spectral object is constructed directly from the source library's functorial
Grothendieck spectral object. Private, fully proved helpers assemble its interval functors
and connecting maps in the functor category, reflect exactness through evaluation, and
establish the first-quadrant bounds. The proof establishes direct-image left exactness
and injective preservation, builds the interval and abutment comparisons, identifies the
assembled bottom edge, and performs the naturality and derived-zero cancellations.

Added proof-only imports of `Sheaf.CategoryTheory.GrothendieckBottomResolutionComparison`
and `Sheaf.Topology.TopologicalTerminalResolutionExtComparison`. Each new module has one
public theorem with its source, full proof in words, and a new DAG node. Updated only the
parent node's proof, proof_deps and proof_origin to follow the implemented argument.
All three modules compile together through lcompile.py, without warnings. No library
build, target edit, interface change, forced adaptation, or arbitrary witness definition
is involved. The spectral object is concrete; comparison witnesses are used inside the
existential theorem proof, and their composite is constrained by the resolution equation.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.exists_topological_leray_spectral_object_augmentation`
(node `lem-sc-topological-leray-spectral-object-augmentation`). Its proof contains no sorry.
The private declarations `exact_of_evaluation`, `exact_arrows_of_evaluation`,
`assembleSpectralObject`, and `assemble_firstQuadrant` are fully proved/constructed.

Added two holes, each exactly the whole proof of its named public theorem:

- `CategoryTheory.grothendieckBottomEdgeMap_eq_resolution`
  (node `lem-sc-grothendieck-bottom-resolution-comparison`), in
  `Sheaf.CategoryTheory.GrothendieckBottomResolutionComparison`.
- `CategoryTheory.exists_topological_terminal_resolution_ext_comparison`
  (node `lem-sc-topological-terminal-resolution-ext-comparison`), in
  `Sheaf.Topology.TopologicalTerminalResolutionExtComparison`.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof of the complete result. The first lower statement has no sheaf or Ext
content; the second has no spectral object or edge. The real Lean argument constructs
the spectral object, joins these independent comparisons, and cancels all transports.
The next worker can prove either comparison independently.

Edge cases checked in the argument: n=0 uses the ordinary derived-zero map with no
incoming differential or sign; identity F and identity comparison give the identity
homology map; zero objects give zero maps. The terminal Hom/section representation
continues to hold for empty spaces (both terminal sections are zero when appropriate).
The terminal comparison allows arbitrary resolutions and augmented comparisons, not
only the selected resolutions. The generic comparison requires acyclicity, not exactness
of F; the target resolution is an acyclic complex for G, not a resolution of F(X).

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
and its use of `thm-sp-grothendieck`'s Cartan--Eilenberg page/filtration presentation.
The source-library Grothendieck spectral object and its canonical edge remain in use.
Removed redundant direct proof imports
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` and
`Mathlib.Algebra.Category.Grp.AB`; their instances remain available through the statement
imports of the new terminal-comparison module, so these Mathlib results are NOT pruned.
The original pushforward-injective and enough-injectives nodes remain needed.

The following project modules leave this item's import closure (comparison includes
all Mathlib imports). This is local route pruning; modules reached elsewhere by targets
are not claimed globally pruned. Each line gives the module and its attached nodes:

- `Sheaf.Algebra.Homology.DoubleComplexSingleRowTotalIso`: `lem-sp-double-complex-single-row-total-iso`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalQuotientComparison`: `lem-sp-double-complex-vertical-quotient-total-comparison`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalSpectralObject`: `lem-sp-double-complex-vertical-spectral-object`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparison`: `lem-sp-double-complex-vertical-tower-comparison`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparisonFinite`: `lem-sp-double-complex-vertical-tower-comparison-finite`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparisonTop`: `lem-sp-double-complex-vertical-tower-comparison-top`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps`: `lem-sp-double-complex-vertical-tower-maps`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalWindow`: `def-sp-double-complex-vertical-window`.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalWindowHomology`: `lem-sp-double-complex-vertical-window-homology`.
- `Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`: `lem-sp-filtered-complex-first-page-cycles-boundaries`.
- `Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison`: `lem-sp-filtered-complex-quotient-image-comparison`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`: `def-sp-filtered-complex-subquotients`.
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`: `lem-sp-filtered-complex-ZB-description`.
- `Sheaf.Algebra.Homology.FirstQuadrantExtendedTotalExact`: `lem-sp-first-quadrant-extended-total-exact`.
- `Sheaf.Algebra.Homology.FirstQuadrantTotalShortExact`: `lem-sp-first-quadrant-total-extend-short-exact`.
- `Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration`: `lem-sp-first-quadrant-vertical-cone-filtration`.
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`: `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
- `Sheaf.Algebra.Homology.RestrictedComplementaryTruncationComparison`: `lem-sp-restricted-complementary-truncation-comparison`.
- `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIso`: `lem-sp-vertical-cutoff-column-quasiiso`.
- `Sheaf.Algebra.Homology.VerticalCutoffQuotientComparison`: `lem-sp-vertical-cutoff-quotient-comparison`.
- `Sheaf.Algebra.Homology.VerticalWindowComponentIso`: `lem-sp-vertical-window-component-iso`.
- `Sheaf.Algebra.Homology.VerticalWindowComponentNaturality`: `lem-sp-vertical-window-component-naturality`.
- `Sheaf.Algebra.Homology.VerticalWindowDegreeIso`: `lem-sp-vertical-window-degree-iso`.
- `Sheaf.Algebra.Homology.VerticalWindowSingleIso`: `lem-sp-vertical-window-single-iso`.
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`: `lem-sp-ce-compatible-homotopy-assembly`.
- `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization`: `lem-weil-pbc-horseshoe-defect-factorization`.
- `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap`: `lem-weil-pbc-horseshoe-degreewise-map`.
- `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection`: `lem-weil-pbc-horseshoe-homotopy-correction`.
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`: `lem-weil-pbc-horseshoe-morphism-lift`, `lem-weil-pbc-horseshoe-preliminary-data`, `lem-weil-pbc-horseshoe-correction`.
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource`: `lem-weil-pbc-horseshoe-morphism-lift-exact-source`.
- `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions`: `lem-sp-horseshoe-prescribed-resolutions`.
- `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows`: `lem-sp-horseshoe-prescribed-row-construction`.
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`: `lem-sp-bounded-filtered-page-core`.
- `Sheaf.CategoryTheory.BoundedFilteredComplexPages`: `thm-sp-spectral-object-yields-canonical-pages`.
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`: `thm-sp-spectral-object-yields`.
- `Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment`: `lem-sp-bounded-filtered-couple-abutment`.
- `Sheaf.CategoryTheory.BoundedFilteredPageConstruction`: `lem-sp-bounded-filtered-page-construction`.
- `Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment`: `lem-sp-ce-acyclic-abutment`.
- `Sheaf.CategoryTheory.CartanEilenbergAcyclicAugmentation`: `lem-sp-ce-acyclic-augmentation`.
- `Sheaf.CategoryTheory.CartanEilenbergAugmentationComparison`: `lem-sp-ce-augmentation-comparison`.
- `Sheaf.CategoryTheory.CartanEilenbergAugmentedComparison`: `lem-weil-pbc-ce-augmented-comparison`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`: `lem-sp-cartan-eilenberg-comparison-homotopy`.
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`: `lem-sp-cartan-eilenberg-comparison-independence`.
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`: `lem-sp-cartan-eilenberg-double-complex-homotopy`.
- `Sheaf.CategoryTheory.CartanEilenbergExists`: `lem-sp-cartan-eilenberg-exists`.
- `Sheaf.CategoryTheory.CartanEilenbergFilteredTruncationComparison`: `lem-sp-ce-filtered-truncation-comparison`.
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`: `lem-weil-pbc-cartesian-eilenberg-functorial`.
- `Sheaf.CategoryTheory.CartanEilenbergPageRealization`: `lem-sp-ce-page-realization`.
- `Sheaf.CategoryTheory.CartanEilenbergPresentation`: `def-sp-cartan-eilenberg-presentation`.
- `Sheaf.CategoryTheory.CartanEilenbergRows`: `def-sp-cartan-eilenberg-rows`.
- `Sheaf.CategoryTheory.CartanEilenbergRowsExists`: `lem-sp-cartan-eilenberg-rows-exists`.
- `Sheaf.CategoryTheory.CartanEilenbergRowsIdentifications`: `lem-sp-cartan-eilenberg-rows-identifications`.
- `Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation`: `lem-sp-ce-second-image-truncation`.
- `Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy`: `lem-sp-ce-vertical-nullhomotopy`.
- `Sheaf.CategoryTheory.DegreewiseFilteredAcyclic`: `lem-sp-degreewise-filtered-acyclic`.
- `Sheaf.CategoryTheory.DegreewiseFilteredStableQuotient`: `lem-sp-degreewise-filtered-stable-quotient`.
- `Sheaf.CategoryTheory.DerivedCoupleExact`: `lem-sp-derived-couple-exact`.
- `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`: `lem-sp-derived-couple-functoriality`.
- `Sheaf.CategoryTheory.DerivedCoupleMapConstruction`: `lem-sp-derived-map-construction`.
- `Sheaf.CategoryTheory.DerivedCoupleMapExactness`: `lem-sp-derived-map-exactness`.
- `Sheaf.CategoryTheory.DoubleComplexBoundedBelowTotal`: `lem-weil-pbc-total-bounded-below`.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential`: `lem-weil-pbc-total-first-filtration-differential`.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap`: `lem-weil-pbc-total-first-filtration-map`.
- `Sheaf.CategoryTheory.DoubleComplexTotal`: `def-sp-double-complex-total`.
- `Sheaf.CategoryTheory.ExactCouple`: `def-sp-exact-couple`.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`: `def-sp-convergence`.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`: `lem-sp-couple-morphism`.
- `Sheaf.CategoryTheory.FilteredCohomologyImage`: `lem-sp-filtered-cohomology-image-finite`.
- `Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles`: `lem-sp-filtered-complex-boundaries-le-cycles`.
- `Sheaf.CategoryTheory.FilteredComplexGradedHomology`: `lem-sp-filtered-complex-graded-homology`.
- `Sheaf.CategoryTheory.FilteredComplexPageDifferential`: `lem-sp-filtered-complex-page-differential`.
- `Sheaf.CategoryTheory.FilteredComplexPageHomology`: `lem-sp-filtered-complex-page-homology`.
- `Sheaf.CategoryTheory.FilteredComplexPositivePages`: `lem-sp-filtered-complex-positive-pages`.
- `Sheaf.CategoryTheory.FilteredComplexSpectralSequence`: `lem-sp-filtered-complex-associated-spectral-sequence-construction`.
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`: `lem-sp-filtered-homotopy-spectral-sequence`.
- `Sheaf.CategoryTheory.FilteredPageTwoModel`: `def-sp-filtered-page-two-model`.
- `Sheaf.CategoryTheory.FilteredStableSubquotient`: `lem-sp-filtered-stable-subquotient-at-bounds`.
- `Sheaf.CategoryTheory.Filtration`: `def-sp-filtration`.
- `Sheaf.CategoryTheory.GrothendieckCanonicalImageFiltration`: `lem-sp-grothendieck-canonical-image-filtration`.
- `Sheaf.CategoryTheory.GrothendieckComposablePair`: `def-sp-composite-acyclicity`.
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`: `thm-sp-grothendieck`.
- `Sheaf.CategoryTheory.HalfPlaneConvergence`: `thm-sp-half-plane-convergence`.
- `Sheaf.CategoryTheory.HalfPlaneDiagonalColimits`: `lem-sp-half-plane-diagonal-colimits`.
- `Sheaf.CategoryTheory.HalfPlaneWeakConvergence`: `lem-sp-half-plane-weak-convergence`.
- `Sheaf.CategoryTheory.HorizontalComparisonLift`: `lem-sp-ce-horizontal-lift`.
- `Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor`: `lem-sp-spectral-object-page-two-functor`.
- `Sheaf.CategoryTheory.SubobjectHomologyStep`: `lem-sp-subobject-homology-step`.
- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`: `lem-sp-cart-eilenberg-left-exact-cohomology`.
- `WeilConjectures.FromJoel.Algebra.Homology.TotalComplex`: no attached node found.
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`: no attached node found.
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`: `thm-sp-double-complex-spectral-sequences`.
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`: no attached node found.
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice`: no attached node found.
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`: no attached node found.

## Where the brief, the DAG or earlier work was wrong

The existing Grothendieck Cartan--Eilenberg theorem constructs pages and filtration data,
not the required terminal Ext normalization of the spectral-object bottom edge. Its
signature does not by itself supply the cocycle formula. The source library already has
the concrete functorial truncation spectral object, canonical interval comparisons and
canonical abutment comparison; the separate CE page model is unnecessary for this item's
statement. The parent unit is `sk-thm-curveestimate`, whose realized statement remains
`thm-sc-proper-cohomology` and whose steps list is empty. No unit statement or step changes.

The new normalized comparison cannot be replaced by the existing bare nonempty natural
Ext/derived-section isomorphism: an arbitrary isomorphism does not determine its value
on extMk. `CohomologyResolutionEvaluationNatural` uses constant-sheaf H, positive degrees,
and endomorphisms; it does not supply the cross-site H-prime cocycle formula. The existing
generic Grothendieck cocycle API concerns the left edge, whereas this item needs the
bottom edge. These distinctions are recorded in the new nodes' search results.

Read sources: [015M](https://stacks.math.columbia.edu/tag/015M),
[015N](https://stacks.math.columbia.edu/tag/015N),
[015J](https://stacks.math.columbia.edu/tag/015J),
[01F2](https://stacks.math.columbia.edu/tag/01F2),
[01FT](https://stacks.math.columbia.edu/tag/01FT), and
[06XR](https://stacks.math.columbia.edu/tag/06XR).
The explicit bottom-augmentation and Hom/section calculations fill details beyond the
source statements, and proof_origin marks them as agent expansions. LeanSearch returned
Internal Server Error for both searches; this is recorded as unavailable, with no
absence verdict. LeanFinder/Loogle, source grep and whole-blueprint search supplied the
other searches. No disputed statement or tool workaround.

## New nodes

`lem-sc-grothendieck-bottom-resolution-comparison`: generic equality between the canonical
bottom edge and homology of a supplied augmented comparison. Its hypotheses allow an
arbitrary abelian target, with acyclicity at F(I). Sources are Tags 015M/015N/015J and the
existing canonical resolution/unit comparisons. Module:
`Sheaf.CategoryTheory.GrothendieckBottomResolutionComparison`.

`lem-sc-topological-terminal-resolution-ext-comparison`: natural Ext comparisons of
terminal sections and the pushforward/sections composite, normalized on arbitrary
resolution cocycles using the generator identity for a. Sources are Tags 01FT/06XR/01F2.
Module: `Sheaf.Topology.TopologicalTerminalResolutionExtComparison`.

Both inherit the parent's chapter, unit and blueprint ancestor with the parent prepended
to via. Both have all three required search kinds and complete argument steps. Neither
restates the spectral-object existence/augmentation theorem. No change record is needed:
existing public signatures and imports are unchanged, and the additions are new modules.

## Second reading by H3

1. Compared the delivered parent module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports, private
   helpers, and proof bodies differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no compiler
   errors, forbidden declarations, or unnamed `sorry`s. The two split theorems are the
   only remaining holes and each has a matching DAG node and proof docstring. Verdict:
   pass.
3. Read both split statements and checked the zero-degree, identity, and zero-object
   cases. Each is a strictly smaller comparison result and neither restates the parent
   spectral-object theorem. Repository and Mathlib searches found no existing theorem
   with either statement. Verdict: pass.
4. Checked the proof from the target downward. The assembled functor-category spectral
   object is concrete, the first-quadrant proof is by evaluation, and the two remaining
   comparisons are exactly the independent unresolved steps. The removed Grothendieck
   page imports are unused and listed above. Verdict: pass.
5. Compared the parent and new DAG nodes with the Lean declarations. `proof`,
   `proof_deps`, and `proof_origin` follow the imports and calls in the code; the unit
   record and realized route are unchanged. Verdict: pass.

Changed nothing during this second reading; the delivered proofs and decomposition are
consistent with the statements and the stage-3 contract.
