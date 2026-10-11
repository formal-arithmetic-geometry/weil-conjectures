/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift

/-!
# The comonoidal comparison of an additive functor commutes with shifts
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma commShift_mapHomologicalComplexδNatTrans_app (K₁ : CochainComplex C ℤ) :
    NatTrans.CommShift
      (F₁ := (curriedTensor C).map₂CochainComplex.obj K₁ ⋙ G.mapHomologicalComplex (.up ℤ))
      (F₂ := G.mapHomologicalComplex (.up ℤ) ⋙
        (curriedTensor D).map₂CochainComplex.obj ((G.mapHomologicalComplex (.up ℤ)).obj K₁))
      ((mapHomologicalComplexδNatTrans (.up ℤ) G).app K₁) ℤ where
  shift_comm n := by
    ext K₂ m : 3
    dsimp
    simp only [Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, commShiftIso_map₂CochainComplex_hom_app,
      Functor.mapHomologicalComplex_map_f]
    refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
    have h' : p + (q + n) = m + n := by simp at h; lia
    erw [Category.comp_id, ← G.map_comp_assoc,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K₁ K₂ _ n p q m h (q + n) (m + n) rfl rfl]
    rw [map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id]
    erw [Functor.map_id, Category.id_comp, Functor.map_zsmul, Preadditive.zsmul_comp,
      map_ιMapBifunctor_mapBifunctorComparisonX _ _ _ _ _ _ _ h']
    erw [ι_mapBifunctorMap_assoc, HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.map_id,
      Category.id_comp, CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ n p q m h (q + n)
        (m + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id]
    erw [Functor.map_id, Category.id_comp, Preadditive.comp_zsmul]
    rfl

end CategoryTheory.Functor.OplaxMonoidal
