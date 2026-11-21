/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nonzero maximal minors of injective matrices over fields

Source: Stacks Project, Algebra, Tags 00MY, 00MW (1), (3), and 00MV, specialized to a field.
-/

@[expose] public section

universe u

namespace Matrix

/-- An injective `p × n` matrix over a field has `n ≤ p` and a nonzero maximal minor on
an increasing selection of rows and all columns. For zero columns the row selection is
empty and its determinant is one.

Source: Stacks Project, Algebra, Tags 00MY, 00MW (1), (3), and 00MV, specialized to a field. -/
theorem exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective
    {K : Type u} [Field K] {n p : ℕ} (B : Matrix (Fin p) (Fin n) K)
    (hinj : Function.Injective B.mulVec) :
    n ≤ p ∧ ∃ r : Fin n → Fin p, StrictMono r ∧
      (B.submatrix r id).det ≠ 0 ∧ (n = 0 → (B.submatrix r id).det = 1) := by
  classical
  obtain ⟨g, hg⟩ := B.toLin'.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : Matrix (Fin n) (Fin p) K := LinearMap.toMatrix' g
  have hCB : C * B = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have hsum := (cauchy_binet n p C B).1
  rw [hCB, det_one] at hsum
  have hex : ∃ S : {S : Finset (Fin p) // S.card = n},
      (B.submatrix (S.val.orderEmbOfFin S.property) id).det ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ S : {S : Finset (Fin p) // S.card = n},
        (C.submatrix id (S.val.orderEmbOfFin S.property)).det *
          (B.submatrix (S.val.orderEmbOfFin S.property) id).det) = 0 := by
      apply Finset.sum_eq_zero
      intro S _
      rw [h S, mul_zero]
    exact one_ne_zero (hsum.trans hz)
  obtain ⟨S, hS⟩ := hex
  have hnp : n ≤ p := by
    simpa only [S.property, Fintype.card_fin] using Finset.card_le_univ S.val
  refine ⟨hnp, S.val.orderEmbOfFin S.property,
    (S.val.orderEmbOfFin S.property).strictMono, hS, ?_⟩
  intro hn
  subst n
  simp

end Matrix
