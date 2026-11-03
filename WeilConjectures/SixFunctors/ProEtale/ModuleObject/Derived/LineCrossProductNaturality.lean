/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor

/-! # Naturality of a degree-zero cross product

Source: Step 9 of the point-section transport argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical coefficient comparison followed by a degree-zero realization is
natural in both factors.
Source: blueprint `sk-thm-frobenius`, twist removal; Step 9 of point transport.
Proof: compose naturality of the coefficient comparison in its complex and module
arguments, then use the reconstruction square and the interchange law for tensor.
(blueprint: lem-pod-point-line-cross-product-natural) -/
theorem line_cross_product_naturality
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' X X' : DerivedCategory (ModuleCat.{u} R)}
    {M M' : ModuleCat.{u} R}
    (e : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅ X)
    (e' : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M' ≅ X')
    (f : K ⟶ K') (g : X ⟶ X') (h : M ⟶ M')
    (he : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map h ≫ e'.hom =
      e.hom ≫ g) (q : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map f ⊗ₘ h) ≫
        Etale.canonicalCoefficientMap R K' M' q ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map (K' ◁ e'.hom) =
      Etale.canonicalCoefficientMap R K M q ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map (K ◁ e.hom) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map (f ⊗ₘ g) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  have hK := Etale.canonicalCoefficientMap_natural_K R K K' M q f
  have hM := Etale.canonicalCoefficientMap_natural_M R K' M M' q h
  calc
    _ = (H.map f ⊗ₘ 𝟙 M) ≫ (𝟙 (H.obj K') ⊗ₘ h) ≫
        Etale.canonicalCoefficientMap R K' M' q ≫ H.map (K' ◁ e'.hom) := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
      rfl
    _ = Etale.canonicalCoefficientMap R K M q ≫
        H.map (f ▷ S.obj M) ≫ H.map (K' ◁ S.map h) ≫ H.map (K' ◁ e'.hom) := by
      rw [reassoc_of% hM, reassoc_of% hK]
      rfl
    _ = _ := by
      change Etale.canonicalCoefficientMap R K M q ≫
        H.map (f ▷ S.obj M) ≫ H.map (K' ◁ S.map h) ≫ H.map (K' ◁ e'.hom) =
          Etale.canonicalCoefficientMap R K M q ≫
            H.map (K ◁ e.hom) ≫ H.map (f ⊗ₘ g)
      simp only [← H.map_comp]
      congr 2
      rw [← whiskerLeft_comp, he, whiskerLeft_comp]
      simp only [tensorHom_def]
      rw [← whisker_exchange_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
