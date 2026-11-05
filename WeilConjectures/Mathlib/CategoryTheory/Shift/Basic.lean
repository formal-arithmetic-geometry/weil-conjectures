/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Detecting isomorphisms on shifted test objects

In a category with a shift by `ℤ`, every object is isomorphic to a shift `N⟦n⟧` (namely of
`N = X⟦-n⟧`). Hence a morphism `u` is an isomorphism as soon as composition with `u` is bijective
on morphisms out of all objects of the form `N⟦n⟧`
(`CategoryTheory.isIso_of_bijective_comp_shift`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C] [HasShift C ℤ]

omit [HasShift C ℤ] in
/-- Changing the sum in `shiftFunctorAdd'` amounts to composing with an `eqToHom`. -/
@[reassoc]
lemma shiftFunctorAdd'_inv_app_comp_eqToHom {A : Type*} [AddMonoid A] [HasShift C A]
    (a b c c' : A) (h : a + b = c) (h' : a + b = c') (X : C) :
    (shiftFunctorAdd' C a b c h).inv.app X ≫ eqToHom (by rw [← h, ← h']) =
      (shiftFunctorAdd' C a b c' h').inv.app X := by
  subst h h'
  simp

end CategoryTheory
