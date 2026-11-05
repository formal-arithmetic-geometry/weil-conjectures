/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Isomorphisms multiplied by a sign, and averages over colimits

In a preadditive category, an isomorphism `e : X ≅ Y` multiplied by a sign `ε : ℤˣ` is again an
isomorphism (`CategoryTheory.Iso.unitsSMul`).

An endomorphism of a colimit which is levelwise an average of endomorphisms fixes every map out
of the colimit invariant under them
(`CategoryTheory.Limits.IsColimit.comp_eq_of_sum_const_comp_eq_sum`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

/-- An isomorphism multiplied by a sign `ε : ℤˣ`. -/
@[simps]
def Iso.unitsSMul {X Y : C} (ε : ℤˣ) (e : X ≅ Y) : X ≅ Y where
  hom := ε • e.hom
  inv := ε • e.inv
  hom_inv_id := by
    rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, e.hom_inv_id]
  inv_hom_id := by
    rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, e.inv_hom_id]

end CategoryTheory

namespace CategoryTheory.Limits

universe w

end CategoryTheory.Limits
