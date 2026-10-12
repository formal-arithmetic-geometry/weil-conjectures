/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Internal hom comparisons at dualizable objects

A monoidal functor `F : C ⥤ D` between monoidal closed categories has comparison maps
`F [A, B] ⟶ [F A, F B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). If `A` has a
dual, then `[A, B] ≅ Aᘁ ⊗ B` and `[F A, F B] ≅ F Aᘁ ⊗ F B`, and the comparison map is identified
with the inverse of the tensorator `F (Aᘁ ⊗ B) ≅ F Aᘁ ⊗ F B`; hence it is an isomorphism
(`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_of_isDualizable`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

namespace MonoidalClosed

variable [MonoidalClosed C]

/-- If `Y` is a left dual of `X`, the transpose of the inverse of `(ihom X).obj Z ≅ Y ⊗ Z` is
the evaluation `X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z ⟶ 𝟙_ C ⊗ Z ≅ Z`. -/
lemma whiskerLeft_ihomObjIsoTensor_inv_ev (Y X : C) [ExactPairing Y X] (Z : C) :
    X ◁ (ihomObjIsoTensor Y X Z).inv ≫ (ihom.ev X).app Z =
      (α_ _ _ _).inv ≫ ε_ Y X ▷ Z ≫ (λ_ Z).hom := by
  have h := (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) Z
  rw [tensorLeftAdjunction_counit_app] at h
  dsimp only [ihom.ihom_adjunction_counit] at h
  simpa [ihomObjIsoTensor, ihomIsoTensorLeft, Adjunction.rightAdjointUniq_inv_app] using h

end MonoidalClosed

/-- **Monoidal functors commute with internal homs out of dualizable objects.** For a monoidal
functor `F : C ⥤ D` between monoidal closed categories, `C` braided, and a dualizable object
`A` of `C`, the comparison map `F [A, B] ⟶ [F A, F B]` is an isomorphism: under
`[A, B] ≅ Aᘁ ⊗ B` and `[F A, F B] ≅ F Aᘁ ⊗ F B` it is the inverse of the tensorator. -/
theorem Functor.Monoidal.isIso_ihomComparison_app_of_isDualizable [BraidedCategory C]
    [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.Monoidal] {A : C}
    (hA : IsDualizable A) (B : C) :
    IsIso ((ihomComparison F A).natTrans.app B) := by
  obtain ⟨_⟩ := hA
  let := BraidedCategory.exactPairing_swap A Aᘁ
  let := ExactPairing.map F Aᘁ A
  have hε : ε_ (F.obj Aᘁ) (F.obj A) = μ F A Aᘁ ≫ F.map (ε_ Aᘁ A) ≫ η F := rfl
  have h : F.map (ihomObjIsoTensor Aᘁ A B).inv ≫ (ihomComparison F A).natTrans.app B =
      δ F Aᘁ B ≫ (ihomObjIsoTensor (F.obj Aᘁ) (F.obj A) (F.obj B)).inv := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_left, uncurry_eq, uncurry_eq,
      ihomComparison_ev, μ_natural_right_assoc, ← F.map_comp,
      whiskerLeft_ihomObjIsoTensor_inv_ev, whiskerLeft_ihomObjIsoTensor_inv_ev, hε]
    rw [F.map_comp, F.map_comp, Functor.Monoidal.map_associator_inv,
      Functor.Monoidal.map_whiskerRight]
    simp
    simp only [Functor.Monoidal.map_associator_inv, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  have : IsIso (F.map (ihomObjIsoTensor Aᘁ A B).inv ≫ (ihomComparison F A).natTrans.app B) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (ihomObjIsoTensor Aᘁ A B).inv) _

end CategoryTheory
