/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# The intersection of two subobjects as a kernel

In an abelian category, the intersection `S ⊓ T` of two subobjects of an object `X` is the
kernel of the composition of `T.arrow : (T : C) ⟶ X` with the projection `X ⟶ X ⧸ S`.

## Main results

- `CategoryTheory.Subobject.isLimitKernelForkInf`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

@[reassoc (attr := simp)]
lemma ofLE_inf_comp_arrow_comp_cokernel_π (S T : Subobject X) :
    ofLE (S ⊓ T) T _root_.inf_le_right ≫ T.arrow ≫ cokernel.π S.arrow = 0 := by
  rw [← Category.assoc, ofLE_arrow, ← ofLE_arrow (_root_.inf_le_left (a := S) (b := T)),
    Category.assoc, cokernel.condition, comp_zero]

/-- In an abelian category, the intersection `S ⊓ T` of two subobjects of `X` is the kernel
of the composition of `T.arrow` with the projection `X ⟶ X ⧸ S`. -/
noncomputable def isLimitKernelForkInf (S T : Subobject X) :
    IsLimit (KernelFork.ofι (ofLE (S ⊓ T) T _root_.inf_le_right)
      (ofLE_inf_comp_arrow_comp_cokernel_π S T)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    rw [← Category.assoc] at hk
    have hS : S.Factors (k ≫ T.arrow) := by
      rw [← Abelian.monoLift_comp S.arrow (k ≫ T.arrow) hk]
      exact factors_comp_arrow _
    refine ⟨factorThru _ _ ((inf_factors _).2 ⟨hS, factors_comp_arrow k⟩), ?_⟩
    rw [← cancel_mono T.arrow, Category.assoc, ofLE_arrow, factorThru_arrow])

end CategoryTheory.Subobject
