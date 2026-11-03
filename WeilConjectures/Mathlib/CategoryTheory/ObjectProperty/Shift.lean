/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.Mathlib.CategoryTheory.EqToHom
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Shifts on full subcategories, up to heterogeneous equality

For a property `P` of objects of a category with a shift which is stable under shifts, the
shift on `P.FullSubcategory` is (by construction) the ambient one: shifted objects are the
ambient shifts (`ObjectProperty.shiftFunctor_obj_obj`) and the shift comparisons of `P.ι` are
identities (`ObjectProperty.ι_commShiftIso_hom_app_heq`). We deduce that the comparison
`P.liftCompιIso G hG` commutes with shifts for any shift structure on the lift whose
comparisons are the ambient ones (`ObjectProperty.liftCompιIso_hom_commShift_of_heq`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- The inclusion of a shift-stable full subcategory has identity shift comparisons. -/
theorem ι_commShiftIso_hom_app_heq (P : ObjectProperty C) [P.IsStableUnderShift ℤ] (n : ℤ)
    (Z : P.FullSubcategory) : (P.ι.commShiftIso n).hom.app Z ≍ 𝟙 (Z.obj⟦n⟧) := by
  with_unfolding_all exact HEq.rfl

/-- Shifted objects of a shift-stable full subcategory are the ambient shifts. -/
theorem shiftFunctor_obj_obj (P : ObjectProperty C) [P.IsStableUnderShift ℤ] (n : ℤ)
    (Z : P.FullSubcategory) : (Z⟦n⟧).obj = Z.obj⟦n⟧ := by
  with_unfolding_all rfl

/-- A lifted functor whose shift comparisons are the ambient ones commutes with the
identity comparison to the ambient functor. -/
theorem liftCompιIso_hom_commShift_of_heq (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (G : C ⥤ D) (hG : ∀ X, P (G.obj X)) [G.CommShift ℤ] {_ : (P.lift G hG).CommShift ℤ}
    (hs : ∀ X (n : ℤ),
      (((P.lift G hG).commShiftIso n).hom.app X).hom ≍ (G.commShiftIso n).hom.app X) :
    NatTrans.CommShift (P.liftCompιIso G hG).hom ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, ObjectProperty.liftCompιIso, Iso.refl_hom,
    NatTrans.id_app, ObjectProperty.ι_map]
  apply eq_of_heq
  exact (comp_heq_of_heq_id _ _ rfl (heq_of_eq ((shiftFunctor D n).map_id _))).trans
    ((comp_heq_of_heq_id _ _ (shiftFunctor_obj_obj P n _)
    (ι_commShiftIso_hom_app_heq P n _)).trans
      ((hs X n).trans (heq_of_eq (Category.id_comp _)).symm))

end CategoryTheory.ObjectProperty
