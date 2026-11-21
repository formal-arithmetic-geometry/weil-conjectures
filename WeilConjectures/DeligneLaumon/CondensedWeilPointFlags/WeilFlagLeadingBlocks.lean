/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Invertible leading blocks in an upper triangular Weil matrix
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.CondensedWeilPointFlags

/-- All leading blocks of an upper triangular matrix with unit diagonal are invertible. -/
theorem leading_blocks_isUnit {K : Type u} [Field K] {d : ℕ}
    (C : Matrix (Fin d) (Fin d) K) (hC : C.IsUpperTriangular)
    (hdiag : ∀ i, IsUnit (C i i)) (j : ℕ) (hj : j ≤ d) :
    IsUnit (C.submatrix (Fin.castLE hj) (Fin.castLE hj)) := by
  classical
  have hupper : (C.submatrix (Fin.castLE hj) (Fin.castLE hj)).IsUpperTriangular := by
    intro a b hab
    exact hC hab
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_of_isUpperTriangular hupper]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (hdiag (Fin.castLE hj i)).ne_zero

end WeilConjectures.CondensedWeilPointFlags
