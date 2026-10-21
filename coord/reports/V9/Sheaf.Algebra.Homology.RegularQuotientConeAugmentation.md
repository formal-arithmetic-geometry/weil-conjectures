## What changed

Proved the principal quotient augmentation by a flat-term short exact sequence and K-flat
resolution comparison. Constructed the strict augmentation from the ordinary coefficient unit,
then used universal cochain descent and a normalized derived adjunction to obtain the prescribed
comparison and unit identity. The auxiliary generic descent and derived-adjunction lemmas allow
independent derived-category universes.

Extracted the original scalar/cone constructions verbatim into RegularQuotientConeBasic and
publicly re-exported them. Generalized the existing normalized ExtensionTensorComparison proof
to independent site/coefficient universes in its own namespace. No WeilConjectures file is changed.
Corrected the coordinate comment to scalar-first `1 ⊗ y`, matching the unchanged section
equation and component signature.
Change record: coord/changes/V9-regular-quotient-cone-basic.md.

## Proved and sorry left

Closed the original hole
SheafOfModules.RegularQuotientCone.nonempty_augmentation
(node lem-cbc-regular-quotient-cone-augmentation): one of one original holes.
Added zero holes and split off zero unfinished results. No sorry remains in any delivered module.

The new proved results include chainAugmentation_components, inclusion_chainAugmentation,
section_image_zero, scalar_restriction_zero, coefficientUnit_zero, cone_quasiIso,
exists_extensionTensorComparison, tensorPresheafUnit_naturality,
tensorPresheafUnit_whiskerRight_apply, regularTensorIso_inv_apply,
coefficient_shortExact_of_flat, chainAugmentation_quasiIso,
exists_cochainDerivedAdjunction and exists_cochainAugmentationDescent.
The tensor comparison and regular unitor are explicit constructions; no arbitrary data is
selected from a holed existence theorem. The final file compiles without warnings (13.8 seconds); delivery checks follow.

## No longer needed

The item's proof no longer uses the total-tensor/homotopy/cone-sign theorem
lem-weil-pbc-total-tensor-homotopy-cone-signs: flat resolutions and degreewise tensor exactness
replace the arbitrary-K-flat total-tensor argument. No proof of K-flatness of the two-term
coefficient cone is needed. Scalar cone invariance follows directly from a morphism of
mapping-cone triangles, so the direct dependency on lem-pur-quasi-iso-cone-acyclic and import
WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic are removed.

Removed Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction and its direct node
lem-pur-sheaf-ring-derived-coefficient-adjunction: use the ordinary normalized adjunction and
a general cochain derived-adjunction lemma, which supports independent localization universes.
Removed Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients and node
lem-weil-pbc-site-derived-tensor-descent: direct pointwise Kan descent supplies the natural
isomorphism, with the exact specified universal counit. The short-exact cone projection,
localization universal property, K-flat resolution and derived-change-of-rings model remain
needed through the new lemmas. In particular,
Mathlib.Algebra.Homology.HomotopyCategory.ShortExact is now imported by
RegularQuotientConeQuasiIso, and the functionality of Mathlib.CategoryTheory.Localization.Predicate
is used by CochainAugmentationDescent through its derived-category imports. Their direct
imports and tool-use entries leave the item; the two mathematical nodes remain in the route.
def-pc-kflat-complex remains a statement dependency rather than a separate proof step.
No module is withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically valid but longer than necessary. Its derived coefficient
adjunction statement uses a common localization universe; the item's statement has independent
ones. The generic cochain argument retains the item's universes and normalizes the given
cochain counit directly. The ordinary normalized tensor comparison similarly needed its site
and coefficient universes separated. No statement has been weakened.

## New nodes

- def-cbc-regular-quotient-cone-basic records the original common constructions in their new module.
- lem-cbc-regular-quotient-cone-chain records the strict augmentation formulas and cone invariance.
- lem-cbc-extension-tensor-comparison-independent records the normalized tensor comparison and
  regular unitor for independent universes.
- lem-cbc-regular-quotient-flat-sequence tensors the coefficient sequence and transports its maps.
- lem-cbc-regular-quotient-cone-quasi-iso uses flat terms and a K-flat resolution comparison.
- lem-cbc-cochain-derived-adjunction transfers a universal cochain pair to the homotopy setting
  and applies the existing compatible derived-adjunction theorem.
- lem-cbc-cochain-augmentation-descent constructs the prescribed comparison using its universal
  cochain counit.

Change record: coord/changes/V9-regular-quotient-cone-basic.md.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
