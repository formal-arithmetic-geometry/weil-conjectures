/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Isomorphisms multiplied by a sign

In a preadditive category, an isomorphism `e : X ≅ Y` multiplied by a sign `ε : ℤˣ` is again an
isomorphism (`CategoryTheory.Iso.unitsSMul`).
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
