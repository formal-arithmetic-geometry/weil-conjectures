/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition

/-! # Composition of derived direct-image transitions

Source: Stacks Tag 09Z1, canonical restriction maps, and Mathlib's mate calculus.
(blueprint: lem-sbc-lower-star-plus-transition-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Derived direct-image transitions compose after the pullback composition comparison.

Source: Stacks Tag 09Z1, restriction maps for higher direct images; the mate calculation
is Mathlib `mateEquiv_vcomp`, specialized to identity functors on the common base.
(blueprint: lem-sbc-lower-star-plus-transition-comp)

Proof: the transition for a triangle is the adjunct of its pullback comparison followed
by pullback of the counit. Apply the inverse hom-set equivalence for the adjunction
D(h₁)^* ⊣ R(h₁)_* to the desired equality. Naturality of that equivalence and of the
comparison for a₁ moves the first transition inside D(a₁)^*. The counit for h₂ followed
by its own adjunct cancels by a triangle identity. The resulting composite is the
comparison for (a₁,h₂), then D(a₁)^* of the comparison for (a₂,h), then
D(a₁)^*D(a₂)^* of the counit for h, followed by the inverse comparison for a₁,a₂.
Associativity `upperStarCompDerivedPlus_assoc` identifies the first two comparisons
with the comparison for (a₁ ≫ a₂,h) followed by the comparison for a₁,a₂.
Naturality of the latter moves the counit past it; its inverse cancels. What remains
is exactly the adjunct defining the composite transition. Injectivity of the hom-set
equivalence proves the equality. Transport along wh₂ and wh₁ uses eqToIso, with proof
irrelevance ensuring independence of the chosen witnesses. No cartesianness, properness,
or degree bound is used. Identity triangles satisfy the same proof by the unit laws,
and the zero complex gives the equality of zero maps.
-/
theorem Etale.lowerStarPlusTransition_comp
    {X Y Y₁ Y₂ : Scheme.{u}} (h : Y ⟶ X)
    (a₂ : Y₂ ⟶ Y) (h₂ : Y₂ ⟶ X) (wh₂ : a₂ ≫ h = h₂)
    (a₁ : Y₁ ⟶ Y₂) (h₁ : Y₁ ⟶ X) (wh₁ : a₁ ≫ h₂ = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a₂ h h₂ wh₂ K ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app K) =
      Etale.lowerStarPlusTransition Λ (a₁ ≫ a₂) h h₁
        (by rw [Category.assoc, wh₂, wh₁]) K := by sorry

end AlgebraicGeometry
