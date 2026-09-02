/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

/-!
# Determinants detect linear independence of a finite family of functions

A finite family of functions `v : Fin r → ι → K` with values in a field is linearly
independent if and only if some `r × r` minor `(v j (n i))` has nonzero determinant. Since a
nonzero determinant stays nonzero under a field extension, linear independence of such a
family is insensitive to enlarging the field of coefficients.

## Main statements

- `LinearIndependent.exists_det_ne_zero`: a finite linearly independent family of functions
  `ι → K` has a nonvanishing square minor, i.e. finitely many coordinates already witness the
  independence.
- `LinearIndependent.map_algebraMap`: linear independence of a finite family of functions
  `ι → K` is preserved by pushing the values along a field extension `K → L`.
-/

open Finset

section Minors

variable {K : Type*} [Field K] {ι : Type*}

/-- Finitely many coordinates detect linear independence of a finite family of functions:
if `v : Fin r → ι → K` is linearly independent, then there are indices `n : Fin r → ι` such
that the square matrix `(v j (n i))` has nonzero determinant. -/
theorem LinearIndependent.exists_det_ne_zero {r : ℕ} {v : Fin r → ι → K}
    (hv : LinearIndependent K v) :
    ∃ n : Fin r → ι, (Matrix.of fun i j => v j (n i)).det ≠ 0 := by
  induction r with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ r ih =>
    obtain ⟨n₀, hn₀⟩ := ih (hv.comp Fin.castSucc (Fin.castSucc_injective r))
    by_contra! hcon
    -- the cofactors of the last row do not depend on the last index
    set c : Fin (r + 1) → K := fun j => (-1) ^ ((Fin.last r : ℕ) + (j : ℕ)) *
      (Matrix.of fun i j' : Fin r => v (j.succAbove j') (n₀ i)).det with hc
    have key : ∀ m : ι, ∑ j, c j * v j m = 0 := by
      intro m
      obtain ⟨n, hnc, hnl⟩ : ∃ n : Fin (r + 1) → ι,
          (∀ i, n i.castSucc = n₀ i) ∧ n (Fin.last r) = m :=
        ⟨Fin.snoc n₀ m, fun i => by simp, by simp⟩
      have h := hcon n
      rw [Matrix.det_succ_row _ (Fin.last r)] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsub : (Matrix.of fun i j => v j (n i)).submatrix
            (Fin.last r).succAbove j.succAbove
          = Matrix.of fun i j' : Fin r => v (j.succAbove j') (n₀ i) := by
        ext i j'
        simp [hnc]
      rw [hsub]
      simp only [hc, Matrix.of_apply, hnl]
      ring
    have hc0 : ∀ j, c j = 0 := by
      refine Fintype.linearIndependent_iff.mp hv c (funext fun m => ?_)
      simpa [Finset.sum_apply] using key m
    have hlast := hc0 (Fin.last r)
    simp only [hc, Fin.succAbove_last] at hlast
    rcases mul_eq_zero.mp hlast with h1 | h2
    · exact pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero (α := K))) h1
    · exact hn₀ h2

end Minors

section Extension

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- Linear independence of a finite family of functions `ι → K` is preserved by pushing the
values along a field extension `K → L`. -/
theorem LinearIndependent.map_algebraMap {r : ℕ} {v : Fin r → ι → K}
    (hv : LinearIndependent K v) : LinearIndependent L fun i => algebraMap K L ∘ v i := by
  obtain ⟨n, hn⟩ := hv.exists_det_ne_zero
  have hdet : (Matrix.of fun i j => algebraMap K L (v j (n i))).det ≠ 0 := by
    have hmap : (Matrix.of fun i j => algebraMap K L (v j (n i))).det
        = algebraMap K L (Matrix.of fun i j => v j (n i)).det :=
      ((algebraMap K L).map_det _).symm
    rw [hmap]
    exact fun h => hn ((map_eq_zero_iff _ (algebraMap K L).injective).mp h)
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hvec : Matrix.mulVec (Matrix.of fun i j => algebraMap K L (v j (n i))) g = 0 := by
    funext k
    have h := congrFun hg (n k)
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      Pi.zero_apply] at h
    rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply, ← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hvec) i

end Extension

