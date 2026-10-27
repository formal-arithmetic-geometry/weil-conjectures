/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Locally closed images of morphisms of groupoids on a field

Source: Stacks Project, More on Groupoid Schemes, Tag 04Q9, in Situation 04Q5;
the immersion consequence uses Schemes, Tag 01IQ
(blueprint: lem-sfb-field-kernel-relation-immersion-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism of absolute groupoid schemes with object scheme `Spec k` has closed
image whenever that image is locally closed. Consequently such a morphism which is
an immersion is a closed immersion. Source: Stacks Project, Tag 04Q9 in Situation
04Q5, and Tag 01IQ for the consequence
(blueprint: lem-sfb-field-kernel-relation-immersion-closed).

Proof plan, following the node:
1. Apply `lem-sfb-field-groupoid-perfect-restriction`. The arrow projections are
   homeomorphisms and commute with the morphism. Surjectivity of the source
   projection identifies the new image with the inverse image of the old image.
   Thus local closedness and closedness transfer, reducing to a perfect field.
2. By `lem-sfb-perfect-field-groupoid-image-closure`, the reduced closure `Z` of
   the image is a groupoid. Apply the same result to the identity of `R₁` to get
   its reduction `A`. Reduction preserves the underlying points
   (`def-weil-pbc-scheme-reduction`), so the map from `A` has the original image.
   Factor it through `Z` using
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`.
3. This factorization commutes with source and target. For unit, inverse and
   composition, compose the desired equality with `Z ⟶ R₂`, use compatibility
   of the original maps, and cancel this closed immersion. It is a monomorphism:
   locally maps out of a quotient are determined by their composites with the
   quotient map, and these equalities glue. This verifies all operation equations
   of `def-a1-groupoid-scheme`, including the equation on composable pairs.
4. Write the image as `O ∩ C` with `O` open and `C` closed. Its closure `Z` lies
   in `C`, so the image is `O ∩ Z`, open and dense in `Z`. By
   `lem-sfb-field-groupoid-open-image-closed` the image is also closed in `Z`.
   Hence it equals `Z` and is closed in `R₂`; transfer back in step 1.
5. An immersion factors as a closed immersion followed by an open immersion
   (`def-weil-closed-immersion`), so its image is locally closed. The first
   conclusion makes that image closed; then
   `lem-weil-pbc-immersion-closed-image-closed-immersion` gives a closed immersion.

No perfectness, finiteness, quasi-compactness or separatedness is assumed.
The composition comparison is the canonical pullback map with identity on
`Spec k`, and with `a` on each arrow coordinate. -/
theorem fieldGroupoid_locallyClosed_image
    (k : Type u) [Field k] {R₁ R₂ : Scheme.{u}}
    (s₁ t₁ : R₁ ⟶ Spec (CommRingCat.of k))
    (e₁ : Spec (CommRingCat.of k) ⟶ R₁) (i₁ : R₁ ⟶ R₁)
    (c₁ : pullback s₁ t₁ ⟶ R₁) (_h₁ : IsGroupoidScheme s₁ t₁ e₁ i₁ c₁)
    (s₂ t₂ : R₂ ⟶ Spec (CommRingCat.of k))
    (e₂ : Spec (CommRingCat.of k) ⟶ R₂) (i₂ : R₂ ⟶ R₂)
    (c₂ : pullback s₂ t₂ ⟶ R₂) (_h₂ : IsGroupoidScheme s₂ t₂ e₂ i₂ c₂)
    (a : R₁ ⟶ R₂) (hs : a ≫ s₂ = s₁) (ht : a ≫ t₂ = t₁)
    (_he : e₁ ≫ a = e₂) (_hi : i₁ ≫ a = a ≫ i₂)
    (_hc : c₁ ≫ a =
      pullback.map s₁ t₁ s₂ t₂ a a (𝟙 (Spec (CommRingCat.of k)))
        ((Category.comp_id s₁).trans hs.symm) ((Category.comp_id t₁).trans ht.symm) ≫ c₂) :
    (IsLocallyClosed (Set.range a) → IsClosed (Set.range a)) ∧
      (IsImmersion a → IsClosedImmersion a) := by
  sorry

end AlgebraicGeometry
