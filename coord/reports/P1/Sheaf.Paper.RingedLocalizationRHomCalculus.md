## What changed

In `Sheaf.Paper.RingedLocalizationRHomCalculus`, proved
`CategoryTheory.ringedLocalization_kflat_models` and
`CategoryTheory.ringedLocalization_tensor_product` without changing any existing
signature, definition, universe, or visibility.

The flatness proof checks finite-limit preservation by tensoring the localization
presheaf sectionwise, then applies
`PresheafOfModules.isFlat_sheafification_obj`. Flat coproducts and the existing
slice-flatness theorem give flat terms after restriction. The existing
bounded-above-flat theorem supplies both K-flatness certificates. The source
library's `CochainComplex.mapBifunctorSingle₁Iso` gives the actual isomorphism
between the total tensor and the ordinary tensor complex.

For the coefficient tensor isomorphism, `IsLocalization.Away.mul'` and
`IsLocalization.algEquiv` give the sectionwise algebra equivalence. The two
restriction composites agree by `IsLocalization.ringHom_ext`; equality on pure
tensors gives a module-presheaf isomorphism. Sheafification and its existing tensor
comparison finish the proof. This uses no domain or nonzero-denominator assumption.
The flat-coproduct argument includes the empty sum, and the single complex has
flat zero terms in every degree other than zero.

Added private proved helpers for localization flatness, flat terms of a bounded
localization complex, the algebra tensor equivalence, compatibility of restriction
maps with algebra maps, and the natural presheaf tensor isomorphism. Added proof
imports for the existing flat-sheafification and flat-coproduct interfaces,
Mathlib flat-module/category comparison and localization base change, and the
source flat-zero and single-tensor APIs. Updated the existing node's proof steps
2--4 and dependency list to describe this route. Steps 1, 5 and 6 still describe
the unfinished proof of the third theorem.

## Proved and sorry left

Original holes: 3. Closed: 2. Added: 0. Split off: 0. Remaining: 1.

Closed:

- `CategoryTheory.ringedLocalization_kflat_models`.
- `CategoryTheory.ringedLocalization_tensor_product`.

Remaining, unchanged as a named theorem with its original source and complete
proof in words:

- `CategoryTheory.ringedLocalizationRHom_calculus`, node
  `lem-weil-pbc-ringed-localization-rhom-calculus`.

These are proofs from existing library declarations, not a decomposition into
new unproved statements. No `sorry` occurs in any new helper or definition.

A scratch proof of the pointwise derived currying isomorphism compiled using
`derivedInternalHom_obj_iso`,
`CochainComplex.isKInjective_homComplex_of_isKFlat`, and
`homComplex_tensorTotal_iso`. For a K-injective representative I of N, compare
RHom(L,N) with Q(Hom(L,I)), then use that Hom(L,I) is K-injective, and apply the
chain currying isomorphism. This does not establish simultaneous naturality or
the final restriction square: arbitrary existential representative comparisons
have no stated normalization ensuring these equations. The third theorem
therefore stays open in full; the scratch argument is not counted as a closed hole.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` (already exposed by the flat interfaces).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `Sheaf.Algebra.Homology.HomTensorTotal`.
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

The completed proofs do not use the unfinished Hom/currying argument. Its planned
DAG dependencies are retained for the remaining theorem. These import removals
remove no module from the transitive import closure: the retained public
interfaces already reach those modules. No globally pruned module is claimed.

The current proof no longer directly needs
`lem-weil-pbc-ringed-site-module-sheafification-exact` or
`lem-pc-sites-module-sheafification-interface`: the existing
`lem-pc-sites-modules-sheafification-flat` packages that argument. Restriction
flatness uses the already stated `lem-weil-pbc-slice-restriction-flat`, rather than
repeating the sheafification/restriction computation. The corresponding proof
steps and direct dependency edges have been updated. The localization-flat
Mathlib leaf remains used through typeclass inference.

## Where the brief, the DAG or earlier work was wrong

No false statement or required definition repair was found. Two existing generic
interfaces make the flatness part shorter than its original expanded proof plan.
The remaining coherence argument needs canonical comparisons, not merely
pointwise existence of comparison isomorphisms; it has not been silently replaced
by the latter. No target or unit route changed, and no new node or change record
was needed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
