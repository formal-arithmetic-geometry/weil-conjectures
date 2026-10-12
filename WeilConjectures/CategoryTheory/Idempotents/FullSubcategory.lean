/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Idempotent completeness of full subcategories

A full subcategory `P.FullSubcategory` of `C` closed under retracts is idempotent complete as
soon as the idempotents of the objects satisfying `P` split in `C`: the image of such an
idempotent is a retract of an object satisfying `P`.

In a preadditive category, a property of objects closed under kernels is closed under retracts:
a retract of `Y` is the kernel of the complementary idempotent of `Y`.

## Main statements

- `CategoryTheory.ObjectProperty.isStableUnderRetracts_of_isClosedUnderKernels`
- `CategoryTheory.Idempotents.isIdempotentComplete_fullSubcategory`
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C]

namespace ObjectProperty

/-- In a preadditive category, a retract `X` of `Y` is a kernel of the complementary idempotent
`𝟙 Y - r ≫ i` of `Y`. -/
def isLimitKernelForkOfRetract [Preadditive C] {X Y : C} (e : Retract X Y) :
    IsLimit (KernelFork.ofι (f := 𝟙 Y - e.r ≫ e.i) e.i (by simp)) :=
  KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ e.r)
    (fun g hg ↦ by
      rw [comp_sub, comp_id, sub_eq_zero] at hg
      rw [assoc, ← hg])
    (fun g _ m hm ↦ by rw [← hm, assoc, e.retract, comp_id])

/-- In a preadditive category, a property of objects closed under kernels is closed under
retracts. -/
lemma isStableUnderRetracts_of_isClosedUnderKernels [Preadditive C] (P : ObjectProperty C)
    [P.IsClosedUnderKernels] : P.IsStableUnderRetracts where
  of_retract e hY := P.prop_of_isLimit_kernelFork (isLimitKernelForkOfRetract e) hY hY

end ObjectProperty

namespace Idempotents

/-- A full subcategory closed under retracts is idempotent complete if the idempotents of the
objects satisfying the property split in the ambient category. -/
lemma isIdempotentComplete_fullSubcategory (P : ObjectProperty C) [P.IsStableUnderRetracts]
    (h : ∀ (X : C) (p : X ⟶ X), P X → p ≫ p = p → IsSplit p) :
    IsIdempotentComplete P.FullSubcategory := by
  rw [isIdempotentComplete_iff_isSplit]
  intro X p hp
  obtain ⟨Y, i, e, h₁, h₂⟩ := h X.obj p.hom X.property
    (by rw [← ObjectProperty.FullSubcategory.comp_hom, hp])
  refine ⟨⟨Y, P.prop_of_retract ⟨i, e, h₁⟩ X.property⟩, P.homMk i, P.homMk e,
    P.hom_ext ?_, P.hom_ext ?_⟩
  · simpa using h₁
  · simpa using h₂

end Idempotents

end CategoryTheory
