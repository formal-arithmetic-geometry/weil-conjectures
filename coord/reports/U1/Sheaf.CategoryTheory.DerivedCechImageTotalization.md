## What changed

Filled all ten proof holes in `Sheaf.CategoryTheory.DerivedCechImageTotalization`.
The descent proof takes the exact, normalized augmentation from
`CechInjectiveImage.cech_injective_image_augmentation`, applies the exact functor H,
and transports it through the finite-total comparison. Its derived isomorphism is
constructed with precisely the required hom, so the normalization equation is reflexive.
The comparison uses the existing `HomologicalComplex₂.mapTotalIso`; finiteness of each
natural-number diagonal is proved explicitly.

`coherentCechImageModel_nonempty` uses the already constructed private
`CechColumnAux.model` via a proof-only `import all`. No coherent-model data are
chosen from an unproved existence statement. Element restriction is additive by
sectionwise evaluation. The slice adjunction and bounded-below injective criterion
prove the column comparison. Resolution and coefficient squares follow by checking
the zero-column inclusion and unit naturality; the derived coefficient equation follows
from the existing right-derived pullback unit equation. Refinement and homotopy
compatibility use the proved normalized-naturality API.

Added only proof imports of the three Čech dependencies, the injective-preservation
API and extension of homotopies. The finite-total theorem is moved before the descent
theorem so the latter can use it. Existing declaration signatures, definitions and
public imports are preserved. The item's DAG proof and dependencies now describe
these proofs. Local transparency attributes expose only the complex constructions
needed by the tactics; no shared definition or transparency option changes.

## Proved and sorry left

Closed 10 of the original 10 holes, with no holes added and no decomposition:

- `CategoryTheory.cechImage_elementPullback_additive`.
- `CategoryTheory.coherentCechImageModel_nonempty`.
- `CategoryTheory.CoherentCechImageModel.derived_cech_image_totalization`.
- `CategoryTheory.CoherentCechImageModel.column_comparison_isIso`.
- `CategoryTheory.CoherentCechImageModel.finite_total_comparison`.
- `CategoryTheory.CoherentCechImageModel.augmentation_resolution_naturality`.
- `CategoryTheory.CoherentCechImageModel.augmentation_refinement_naturality`.
- `CategoryTheory.CoherentCechImageModel.augmentation_coefficient_naturality`.
- `CategoryTheory.CoherentCechImageModel.coefficient_derived_normalization`.
- `CategoryTheory.CoherentCechImageModel.total_map_eq_of_homotopy`.

Every declaration above is attached to `lem-sfb-derived-cech-image-totalization`.
There are no `sorry`s left in the item and no new Lean modules or DAG nodes.
The normal single-file compile passed with no errors or warnings in 32.0 seconds,
within the 60-second limit. Delivery runs its independent axiom probe.

## No longer needed

The general coefficient square is proved directly from hδ, unit naturality and the
existing right-derived unit factorization. Consequently this item's proof no longer
uses `lem-sfb-cech-coefficient-derived-comparison` or its module
`Sheaf.CategoryTheory.CechCoefficientDerivedComparison`. That dependency was not
previously imported, and no withdrawal or global unreachability is claimed.

Removed these old proof-plan imports:

- `WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation`.
- `Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation`.
- `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`.
- `WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic`.
- `WeilConjectures.CategoryTheory.InjectiveModulePresheaf`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses`.
- `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.

The corresponding now-unused direct tool approvals removed from the node are
`lem-trf-topos-localization-site-presentation`,
`lem-pur-kinjective-restrict-localized-universes`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-pur-kinjective-restrict-localized-adjunction-universes`,
`lem-weil-pbc-ringed-site-injective-module-injective-presheaf`,
`lem-sc-injective-presheaf-module-nerve-acyclic`,
`lem-sc-first-quadrant-column-augmentation`,
`lem-trf-bounded-below-derived-adjunction`, and
`lem-sp-derived-injective-resolution-naturality`.
Their mathematics is either supplied inside the actual Čech dependencies or unnecessary
for the stated comparisons. In particular restriction here uses the element site of a
sheaf, so the separate representable-over-site K-injective restriction lemmas are not
needed. Resolution-lift existence is not an additional obligation: the statements accept
the actual map or homotopy as an input. No source-library declaration is removed, and
modules still imported transitively are not claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was required. The old coefficient-comparison
step was more specialized than the generic coefficient-square declarations in this
module; the direct component and unit arguments prove those declarations without it.
All work follows the coherent injective-resolution and finite-total route of the item.
The unit statement and its realized proof steps are unchanged.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
