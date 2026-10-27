/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Retracts as cokernels

In a preadditive category, a retract `X` of `Y` is the cokernel of the idempotent endomorphism
`𝟙 Y - r ≫ i` of `Y` (`CategoryTheory.Retract.isoCokernel`).
-/

@[expose] public section

namespace CategoryTheory.Retract

open Limits

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

/-- A retract `X` of `Y` is the cokernel of the idempotent endomorphism `𝟙 Y - r ≫ i` of `Y`. -/
noncomputable def isoCokernel (e : Retract X Y) [HasCokernel (𝟙 Y - e.r ≫ e.i)] :
    X ≅ cokernel (𝟙 Y - e.r ≫ e.i) where
  hom := e.i ≫ cokernel.π _
  inv := cokernel.desc _ e.r (by simp [Preadditive.sub_comp])
  hom_inv_id := by simp
  inv_hom_id := by
    ext
    have h := cokernel.condition (𝟙 Y - e.r ≫ e.i)
    rw [Preadditive.sub_comp, sub_eq_zero] at h
    simpa using h.symm

end CategoryTheory.Retract
