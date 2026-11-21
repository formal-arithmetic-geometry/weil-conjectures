/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Determinant

/-! # Triangular bases with nonzero diagonal for Weil flags
-/

@[expose] public section
set_option autoImplicit false
universe u
open Module
namespace WeilConjectures.CondensedWeilPointFlags

/-- An invertible operator has an upper triangular basis with unit diagonal entries. -/
theorem exists_triangular_basis_units {K : Type u} [Field K] [IsAlgClosed K]
    (d : ℕ) (A : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    ∃ b : Basis (Fin d) K (Fin d → K),
      (LinearMap.toMatrix b b A.toLinearMap).IsUpperTriangular ∧
      ∀ j, IsUnit (LinearMap.toMatrix b b A.toLinearMap j j) := by
  classical
  obtain ⟨b₀, hb₀⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix A.toLinearMap
  have hd : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  let e := Fin.castOrderIso hd
  let b := b₀.reindex e.toEquiv
  have hb : (LinearMap.toMatrix b b A.toLinearMap).IsUpperTriangular := by
    intro i j hij
    have h := hb₀ (e.symm.strictMono hij)
    simp only [b, LinearMap.toMatrix_apply, Basis.reindex_apply,
      Basis.repr_reindex_apply, id_eq] at h ⊢
    convert h using 1; rfl
  refine ⟨b, hb, ?_⟩
  have hdet := (A.isUnit_det b b).ne_zero
  rw [Matrix.det_of_isUpperTriangular hb, Finset.prod_ne_zero_iff] at hdet
  intro j
  exact isUnit_iff_ne_zero.mpr (hdet j (Finset.mem_univ j))

end WeilConjectures.CondensedWeilPointFlags
