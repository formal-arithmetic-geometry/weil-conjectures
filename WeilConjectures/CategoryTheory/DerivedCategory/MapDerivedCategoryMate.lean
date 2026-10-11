/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit

/-!
# Mates and the functors induced on derived categories

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions of exact functors, and let
`β : u ⋙ f₂ ≅ f₁ ⋙ v` be the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for exact `u` and `v`. Then the
isomorphism induced by `β` on derived categories is the mate of the one induced by `τ`, for the
levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Functor

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂`. -/
noncomputable abbrev mapDerivedCategorySquareIso (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ≅
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  (mapDerivedCategoryCompIso F₁ F₂).symm ≪≫ mapDerivedCategoryNatIso e ≪≫
    mapDerivedCategoryCompIso G₁ G₂

/-- On the image `Qh X` of an object of the homotopy category, the isomorphism
`D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is the image of the
isomorphism induced by `e` on homotopy categories. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : HomotopyCategory A (.up ℤ)) :
    F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) ≫
        (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X ≫
          (mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
  have hF := mapDerivedCategoryCompIso_fach F₁ F₂ X
  have hG := mapDerivedCategoryCompIso_fach G₁ G₂ X
  have he := mapDerivedCategoryNatIso_fach e X
  have hG' : (mapDerivedCategoryCompIso G₁ G₂).hom.app (DerivedCategory.Qh.obj X) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactorsh.hom.app X ≫ DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hF' : F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) ≫
      (mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X) ≫
        (F₁ ⋙ F₂).mapDerivedCategoryFactorsh.inv.app X := by
    rw [← cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactorsh.hom.app X)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hF, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]

end Functor

namespace Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂] [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)

include adj₁ adj₂ in
lemma mapDerivedCategoryAdjunction_mate_Qh_obj
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C₁ (.up ℤ)) :
    adj₂.mapDerivedCategoryAdjunction.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) =
      u.mapDerivedCategory.map
          (adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactorsh.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := adj₂.mapDerivedCategoryAdjunction.unit.naturality
    (u.mapDerivedCategoryFactorsh.inv.app X)
  have h₂ := adj₂.mapDerivedCategoryAdjunction_unit_app_Qh_obj ((u.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp at h₁ h₄
  have h₂' : adj₂.mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj ((u.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactorsh.inv.app X ≫
      adj₂.mapDerivedCategoryAdjunction.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X) ≫ (g₂.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := adj₁.mapDerivedCategoryAdjunction_unit_app_Qh_obj X
  have k₁' : adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactorsh.inv.naturality
    ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp at k₂
  have hR : u.mapDerivedCategoryFactorsh.inv.app X ≫
      u.mapDerivedCategory.map
        (adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((u.mapHomotopyCategory (.up ℤ)).map
        ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hu₂ : (adj₂.mapHomotopyCategory (.up ℤ)).unit.app ((u.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj K)) :=
    mapHomotopyCategory_unit_app_quotient _ adj₂ _
  rw [mapHomotopyCategory_unit_app_quotient, hu₂]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app ((u.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (u.mapHomologicalComplex (.up ℤ)).map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C₂ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

include adj₁ adj₂ in
/-- **The functors induced on derived categories preserve mates**: if `β : u ⋙ f₂ ≅ f₁ ⋙ v` is
the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for the adjunctions `f₁ ⊣ g₁` and `f₂ ⊣ g₂` of exact
functors, then the isomorphism induced by `β` on derived categories is the mate of the one
induced by `τ`, for the levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`. -/
lemma mapDerivedCategoryAdjunction_mate
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map (adj₁.mapDerivedCategoryAdjunction.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C₁)) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj K) =
      adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    adj₂.mapDerivedCategoryAdjunction.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ adj₁.mapDerivedCategoryAdjunction.unit.app K =
      adj₁.mapDerivedCategoryAdjunction.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    adj₁.mapDerivedCategoryAdjunction.unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (mapDerivedCategoryAdjunction_mate_Qh_obj adj₁ adj₂ τ β hβ _)]

end Adjunction

end CategoryTheory
