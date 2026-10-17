/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Properties closed under kernels are stable under retracts

In a preadditive category, a retract `Y` of `X` (with `i : Y ⟶ X`, `r : X ⟶ Y`, `i ≫ r = 𝟙 Y`)
is a kernel of the endomorphism `𝟙 X - r ≫ i` of `X`, through `i`
(`CategoryTheory.Retract.isLimitKernelFork`). Hence a property of objects closed under kernels
is stable under retracts (`CategoryTheory.ObjectProperty.isStableUnderRetracts_of_kernels`).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- A retract `Y` of `X` is the kernel of `𝟙 X - r ≫ i` through `i`. -/
noncomputable def Retract.isLimitKernelFork {X Y : C} (e : Retract Y X) :
    IsLimit (KernelFork.ofι (f := 𝟙 X - e.r ≫ e.i) e.i
      (by rw [Preadditive.comp_sub, Category.comp_id, e.retract_assoc, sub_self])) :=
  KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ e.r)
    (fun g hg ↦ by
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hg
      rw [Category.assoc, ← hg])
    (fun g _ m hm ↦ by rw [← hm, Category.assoc, e.retract, Category.comp_id])

/-- A property of objects of a preadditive category which is closed under kernels is stable
under retracts. -/
lemma ObjectProperty.isStableUnderRetracts_of_kernels (P : ObjectProperty C)
    [P.IsClosedUnderKernels] : P.IsStableUnderRetracts where
  of_retract e hX := P.prop_of_isLimit_kernelFork e.isLimitKernelFork hX hX

end CategoryTheory
