/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.Triangulated.IdempotentCompleteOfCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract

/-! # Cohomological Brown representability for Grothendieck derived categories

Source: Stacks Project, Tag 0F5X, `injectives-.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem representable_of_uliftYoneda_retract
    {C : Type uA} [Category.{w} C] [IsIdempotentComplete C]
    (F : Cᵒᵖ ⥤ Type vH) (E : C)
    (r : Retract (F ⋙ uliftFunctor.{w}) (uliftYoneda.{vH}.obj E)) :
    F.IsRepresentable := by
  let Y := uliftYoneda.{vH} (C := C)
  let p : E ⟶ E := Y.preimage (r.r ≫ r.i)
  have hpmap : Y.map p = r.r ≫ r.i := Y.map_preimage _
  have hp : p ≫ p = p := by
    apply Y.map_injective
    rw [Y.map_comp, hpmap]
    simp only [Category.assoc, r.retract_assoc]
  obtain ⟨G, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split E p hp
  have hsplit : Y.map e ≫ Y.map i = r.r ≫ r.i := by
    rw [← Y.map_comp, hei, hpmap]
  let iso : Y.obj G ≅ F ⋙ uliftFunctor.{w} :=
    { hom := Y.map i ≫ r.r
      inv := r.i ≫ Y.map e
      hom_inv_id := by
        calc
          (Y.map i ≫ r.r) ≫ (r.i ≫ Y.map e) =
              Y.map i ≫ (r.r ≫ r.i) ≫ Y.map e := by simp only [Category.assoc]
          _ = Y.map i ≫ (Y.map e ≫ Y.map i) ≫ Y.map e := by rw [hsplit]
          _ = (Y.map i ≫ Y.map e) ≫ (Y.map i ≫ Y.map e) := by
            simp only [Category.assoc]
          _ = 𝟙 _ := by rw [← Y.map_comp, hie, Y.map_id, Category.id_comp]
      inv_hom_id := by
        calc
          (r.i ≫ Y.map e) ≫ (Y.map i ≫ r.r) =
              r.i ≫ (Y.map e ≫ Y.map i) ≫ r.r := by simp only [Category.assoc]
          _ = r.i ≫ (r.r ≫ r.i) ≫ r.r := by rw [hsplit]
          _ = (r.i ≫ r.r) ≫ (r.i ≫ r.r) := by simp only [Category.assoc]
          _ = 𝟙 _ := by rw [r.retract, Category.id_comp] }
  have hrep : (F ⋙ uliftFunctor.{w}).IsRepresentable :=
    ((Functor.RepresentableBy.equivUliftYonedaIso _ G).symm iso).isRepresentable
  exact Functor.isRepresentable_comp_uliftFunctor_iff.mp hrep

/-- A cohomological functor on the unbounded derived category of a Grothendieck
abelian category taking set-indexed coproducts to products is representable.
Source: Stacks Project, Tag 0F5X, `injectives-. -/
theorem grothendieckDerived_cohomological_isRepresentable
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  have : IsIdempotentComplete (DerivedCategory A) :=
    Pretriangulated.isIdempotentComplete_of_hasCoproducts.{max w vA vH}
  obtain ⟨E, ⟨r⟩⟩ := grothendieckDerived_brown_retract H hH
  exact representable_of_uliftYoneda_retract (H ⋙ forget AddCommGrpCat) E r

end CategoryTheory
