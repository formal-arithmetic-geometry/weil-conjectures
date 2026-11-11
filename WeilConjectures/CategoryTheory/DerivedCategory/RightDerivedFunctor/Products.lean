/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The right derived functor preserves products

Let `F : C ⥤ D` be an additive functor between abelian categories with K-injective
resolutions. If `F` preserves products of shape `J` and products of shape `J` are exact
in `D`, then the unbounded right derived functor `RF : D(C) ⥤ D(D)` preserves products of
shape `J`: it is computed by applying `F` termwise to K-injective complexes, these are closed
under products, and products of complexes are products in `D(D)` since products are exact.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {J : Type*} [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete J) D]
  [HasExactLimitsOfShape (Discrete J) D]

/-- The unbounded right derived functor of an additive functor preserving products of shape
`J` preserves products of shape `J`, provided products of shape `J` are exact in the target. -/
lemma preservesLimitsOfShape_discrete_rightDerivedFunctor (F : C ⥤ D)
    [F.Additive] [PreservesLimitsOfShape (Discrete J) F] :
    PreservesLimitsOfShape (Discrete J) F.rightDerivedFunctor := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : J → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    choose I hI e using fun n ↦ DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    have : ∀ n, (I n).IsKInjective := hI
    have : ∀ n, IsIso (β.app (I n)) := fun n ↦ hβ (I n)
    have : (∏ᶜ I).IsKInjective := CochainComplex.isKInjective_of_isLimitFan (productIsProduct I)
    have : IsIso (β.app (∏ᶜ I)) := hβ _
    have hQ := DerivedCategory.isLimitFanMkQObjOfIsKInjective (productIsProduct I)
    let hK : IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ I))
        fun n ↦ DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv) :=
      Fan.IsLimit.ofIsos hQ (fun n ↦ (e n).some) (Iso.refl _) fun n ↦ by simp
    have hG : IsLimit (Fan.mk (G.obj (∏ᶜ I)) fun n ↦ G.map (Pi.π I n)) :=
      isLimitFanMkObjOfIsLimit G _ _ (productIsProduct I)
    have hQG := DerivedCategory.isLimitFanMkQObj hG
    have hR : IsLimit (Fan.mk (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (∏ᶜ I)))
        fun n ↦ F.rightDerivedFunctor.map (DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv)) :=
      Fan.IsLimit.ofIsos hQG
        (fun n ↦ F.rightDerivedFunctor.mapIso (e n).some ≪≫ (asIso (β.app (I n))).symm)
        (asIso (β.app (∏ᶜ I))).symm fun n ↦ by
          have hn := β.naturality (Pi.π I n)
          dsimp at hn ⊢
          rw [IsIso.inv_comp_eq, ← F.rightDerivedFunctor.map_comp_assoc, assoc, Iso.inv_hom_id,
            comp_id, ← reassoc_of% hn, IsIso.hom_inv_id, comp_id]
    exact preservesLimit_of_preserves_limit_cone hK ((isLimitMapConeFanMkEquiv _ _ _).symm hR)
  exact preservesLimitsOfShape_of_discrete _

end CategoryTheory.Functor
