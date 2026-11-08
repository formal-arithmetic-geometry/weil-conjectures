/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Submission.WeilConjectures.Mathlib.CategoryTheory.EqToHom
public import Mathlib.Algebra.Group.Int.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Shift comparisons of inclusions and lifts of full subcategories -/

@[expose] public section

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type*} [Category* C] {A : Type*} [AddMonoid A] [HasShift C A]
  (P : ObjectProperty C) [P.IsStableUnderShift A]

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
/-- The inherited shift of a full subcategory is the ambient shift on underlying objects. -/
theorem obj_shift_eq (a : A) (K : P.FullSubcategory) : (K⟦a⟧).obj = K.obj⟦a⟧ := rfl

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
/-- The inclusion of a full subcategory commutes with shifts by identities. -/
theorem ι_commShiftIso_hom_app (a : A) (K : P.FullSubcategory) :
    (P.ι.commShiftIso a).hom.app K = eqToHom (P.obj_shift_eq a K) := by
  rfl

/-- The inverse shift comparison of the inclusion of a full subcategory. -/
theorem ι_commShiftIso_inv_app (a : A) (K : P.FullSubcategory) :
    (P.ι.commShiftIso a).inv.app K = eqToHom (P.obj_shift_eq a K).symm := by
  rw [← cancel_epi ((P.ι.commShiftIso a).hom.app K), Iso.hom_inv_id_app,
    ι_commShiftIso_hom_app, eqToHom_trans, eqToHom_refl]

/-- The shift comparison of a lifted functor is the ambient comparison. -/
theorem lift_commShiftIso_hom_app_hom {E : Type*} [Category* E] [HasShift E A]
    (F : E ⥤ C) (hF : ∀ X, P (F.obj X)) [F.CommShift A] (a : A) (X : E) :
    (((P.lift F hF).commShiftIso a).hom.app X).hom =
      (F.commShiftIso a).hom.app X ≫ eqToHom (P.obj_shift_eq a ((P.lift F hF).obj X)).symm := by
  have h := Functor.CommShift.OfComp.map_iso_hom_app (P.liftCompιIso F hF) a X
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, ι_commShiftIso_inv_app, ObjectProperty.ι_map] at h
  refine h.trans ?_
  simp

/-- The lifted shift comparison of a restricted functor agrees with the ambient one. -/
theorem lift_ι_comp_commShiftIso_hom_app_hom_heq {C' : Type*} [Category* C'] [HasShift C' A]
    (Q : ObjectProperty C') [Q.IsStableUnderShift A] (F : C' ⥤ C) [F.CommShift A]
    (hF : ∀ X : Q.FullSubcategory, P ((Q.ι ⋙ F).obj X)) (a : A) (K : Q.FullSubcategory) :
    HEq (((P.lift (Q.ι ⋙ F) hF).commShiftIso a).hom.app K).hom
      ((F.commShiftIso a).hom.app K.obj) := by
  rw [lift_commShiftIso_hom_app_hom, Functor.commShiftIso_comp_hom_app, ι_commShiftIso_hom_app,
    eqToHom_map, Category.assoc]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

end ObjectProperty

end CategoryTheory
