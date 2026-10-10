/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The unitors of cochain complexes commute with the shifts

The unit `𝟙_` of cochain complexes is concentrated in degree `0`, so that no sign appears when
the shift of the second factor of `𝟙_ ⊗ K` is moved out
(`CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom`); the shift of the first factor of
`K ⊗ 𝟙_` is moved out without sign (`CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (K : CochainComplex C ℤ) (n : ℤ)

lemma leftUnitor_inv_mapBifunctorShift₂Iso_hom :
    (λ_ (K⟦n⟧)).inv ≫ (mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n).hom =
      (λ_ K).inv⟦n⟧' := by
  ext i
  change (HomologicalComplex.leftUnitor' (K⟦n⟧)).inv i ≫ _ =
    (HomologicalComplex.leftUnitor' K).inv (i + n)
  rw [HomologicalComplex.leftUnitor'_inv, HomologicalComplex.leftUnitor'_inv]
  have h := ι_mapBifunctorShift₂Iso_hom_f (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n 0 i i
    (zero_add i) (i + n) (i + n) rfl rfl
  erw [assoc, assoc, h]
  simp only [shiftFunctor_obj_X', curriedTensor_obj_obj, zero_mul, Int.negOnePow_zero,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_obj_map,
    Iso.refl_inv, comp_id, one_smul, Iso.cancel_iso_inv_left]
  erw [MonoidalCategory.whiskerLeft_id, id_comp]
  rfl

lemma mapBifunctorShift₂Iso_hom_leftUnitor_hom :
    (mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n).hom ≫
      (λ_ K).hom⟦n⟧' = (λ_ (K⟦n⟧)).hom := by
  rw [← cancel_epi (λ_ (K⟦n⟧)).inv, reassoc_of% leftUnitor_inv_mapBifunctorShift₂Iso_hom,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id]

lemma rightUnitor_inv_mapBifunctorShift₁Iso_hom :
    (ρ_ (K⟦n⟧)).inv ≫ (mapBifunctorShift₁Iso K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n).hom =
      (ρ_ K).inv⟦n⟧' := by
  ext i
  change (HomologicalComplex.rightUnitor' (K⟦n⟧)).inv i ≫ _ =
    (HomologicalComplex.rightUnitor' K).inv (i + n)
  rw [HomologicalComplex.rightUnitor'_inv, HomologicalComplex.rightUnitor'_inv]
  have h := ι_mapBifunctorShift₁Iso_hom_f K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n i 0 i
    (add_zero i) (i + n) (i + n) rfl rfl
  erw [assoc, assoc, h]
  simp only [shiftFunctor_obj_X', curriedTensor_obj_obj, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_map_app, Iso.refl_inv, comp_id,
    Iso.cancel_iso_inv_left]
  erw [MonoidalCategory.id_whiskerRight, id_comp]
  rfl

lemma mapBifunctorShift₁Iso_hom_rightUnitor_hom :
    (mapBifunctorShift₁Iso K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n).hom ≫
      (ρ_ K).hom⟦n⟧' = (ρ_ (K⟦n⟧)).hom := by
  rw [← cancel_epi (ρ_ (K⟦n⟧)).inv, reassoc_of% rightUnitor_inv_mapBifunctorShift₁Iso_hom,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id]

end CochainComplex
