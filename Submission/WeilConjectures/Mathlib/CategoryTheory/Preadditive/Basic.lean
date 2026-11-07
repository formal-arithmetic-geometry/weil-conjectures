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
public import Mathlib.CategoryTheory.Endomorphism

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Isomorphisms multiplied by a sign, averages over colimits, and powers of `n •`

In a preadditive category, an isomorphism `e : X ≅ Y` multiplied by a sign `ε : ℤˣ` is again an
isomorphism (`CategoryTheory.Iso.unitsSMul`).

An endomorphism of a colimit which is levelwise an average of endomorphisms fixes every map out
of the colimit invariant under them
(`CategoryTheory.Limits.IsColimit.comp_eq_of_sum_const_comp_eq_sum`).

If multiplication by `n : ℕ` is invertible on an object `Y`, so is multiplication by every power
`n ^ k` (`CategoryTheory.Preadditive.isIso_pow_nsmul_id`), and a right inverse `t` of
multiplication by `n` satisfies `f = n ^ k • (f ≫ t ^ k)`
(`CategoryTheory.Preadditive.eq_pow_nsmul_comp_pow`).
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

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- If multiplication by `n` is invertible on `Y`, so is multiplication by any power of `n`. -/
lemma isIso_pow_nsmul_id {Y : C} (n : ℕ) [IsIso (n • 𝟙 Y)] (k : ℕ) : IsIso (n ^ k • 𝟙 Y) := by
  induction k with
  | zero =>
    rw [pow_zero, one_smul]
    infer_instance
  | succ k ih =>
    rw [pow_succ, mul_smul, ← Category.id_comp (n • 𝟙 Y), ← Preadditive.nsmul_comp]
    infer_instance

/-- If `t` is a right inverse of multiplication by `n` on `Y`, then multiplying `f ≫ t ^ k` by
`n ^ k` gives back `f`. -/
lemma eq_pow_nsmul_comp_pow {Y Z : C} (n : ℕ) (t : End Y) (ht : (n • 𝟙 Y) ≫ t = 𝟙 Y) (k : ℕ)
    (f : Z ⟶ Y) : f = n ^ k • (f ≫ t ^ k) := by
  induction k generalizing f with
  | zero => rw [pow_zero, one_smul, pow_zero, End.one_def, Category.comp_id]
  | succ k ih =>
    rw [pow_succ', mul_smul, pow_succ, End.mul_def, ← Category.assoc, ← ih (f ≫ t),
      ← Preadditive.comp_nsmul, ← Category.id_comp t, ← Preadditive.nsmul_comp, ht,
      Category.comp_id]

end CategoryTheory.Preadditive
