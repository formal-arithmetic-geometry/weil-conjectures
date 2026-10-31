/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.AlgebraicGeometry.RationalP1LocalizingPreservation
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory

set_option linter.style.haveILetI false

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

/-- Restriction of an exact triangulated ambient functor to triangulated full subcategories.
Source: the exact-restriction step of the rational projective-line unit/counit proof.
The inherited shift structure on a full subcategory and `ObjectProperty.isTriangulated_lift`
produce the restricted structures without any additional mathematical assertion.
(blueprint: lem-sfb-rational-p1-restriction-exactness). -/
theorem rationalP1_restrictedFunctorExactness
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsTriangulated] [Q.IsTriangulated]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ A : P.FullSubcategory, Q (F.obj A.obj)) :
    ∃ s : (Q.lift (P.ι ⋙ F) (fun A ↦ hF A)).CommShift ℤ,
      letI := s
      (Q.lift (P.ι ⋙ F) (fun A ↦ hF A)).IsTriangulated := by
  letI : (Q.lift (P.ι ⋙ F) (fun A ↦ hF A)).CommShift ℤ := inferInstance
  exact ⟨inferInstance, inferInstance⟩
