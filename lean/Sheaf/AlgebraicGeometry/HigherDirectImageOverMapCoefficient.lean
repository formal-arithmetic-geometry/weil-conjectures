/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverCoefficient

/-! # The over-W transition as a single mapped coefficient composite

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical transition maps.
(blueprint: sbc-lem-higher-image-over-map-coefficient).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] lowerStarPlusTransition

/-- Identify the homology map of the combined derived coefficient morphism with
 the canonical transition for coefficients restricted from W.
Source: Stacks Project, Tags 03Q8 and 09Z1, the canonical transition construction.
(blueprint: sbc-lem-higher-image-over-map-coefficient).

Proof: Let B₀=(B^*G)[0], A₀=(A^*G)[0], and M₀=(f^*B^*G)[0]. Write
s:f^*B₀→M₀ for the single-complex comparison and c:M₀→A₀ for the image under
the single functor of the inverse-image composition identification. Let R be the
derived direct image along A→S, H degree-q homology, and l the derived triangle
transition from the direct image of B₀ to R(f^*B₀). The left side is H(l ≫ R(s ≫ c)).
Functoriality of R gives R(s ≫ c)=R(s) ≫ R(c). Associativity gives
l ≫ R(s ≫ c)=(l ≫ R(s)) ≫ R(c). Functoriality of H gives
H(l ≫ R(s ≫ c))=H(l ≫ R(s)) ≫ H(R(c)). The first factor is exactly
higherDirectImageTransition by its definition; composing it with the second
factor is exactly higherDirectImageOverMap by its definition. This argument
is purely functorial and holds for every integer q, zero sheaves and identity
arrows, without geometric finiteness assumptions. No object is chosen. -/
theorem higherDirectImageOverMap_coefficient
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) :
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
      (lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])
        (higherDirectImageRawOverComplex Λ G B) ≫
        R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          (higherDirectImageRawOverCoefficient Λ G f)) =
      higherDirectImageOverMap Λ k G q f := by sorry

end AlgebraicGeometry.Etale
