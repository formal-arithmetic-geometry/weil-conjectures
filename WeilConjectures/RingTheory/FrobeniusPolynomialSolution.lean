/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.LinearAlgebra.SemilinearFrobenius

/-!
# Geometric points of a Frobenius polynomial solution algebra

Every inhomogeneous Frobenius polynomial system has a solution over an algebraically closed field
of characteristic `p`.

## Implementation details

The coefficient matrix defines a Frobenius-semilinear endomorphism of `K^n`, and the
Lang–Steinberg theorem provides the solution vector; evaluation at it factors through the
quotient.

## References

* [Stacks, Tag 0GKU] (proof)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open MvPolynomial

namespace Algebra

/-- Every inhomogeneous Frobenius polynomial system has a solution over an
algebraically closed field of characteristic `p`.
-/
theorem exists_frobenius_polynomial_solution
    (R : Type u) [CommRing R] (K : Type v) [Field K] [Algebra R K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (a : Fin n → Fin n → R) (b : Fin n → R) :
    Nonempty ((MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range
      (fun i : Fin n ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p))) →ₐ[R] K) := by
  classical
  let L : (Fin n → K) →ₛₗ[frobenius K p] (Fin n → K) :=
    { toFun := fun x i ↦ ∑ j, algebraMap R K (a i j) * x j ^ p
      map_add' := by
        intro x y
        ext i
        simp [add_pow_char, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, frobenius_def]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  obtain ⟨x, hx⟩ := LinearMap.Frobenius.surjective_sub_id L (fun i ↦ algebraMap R K (b i))
  let r : Fin n → MvPolynomial (Fin n) R :=
    fun i ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p
  have hrel (i : Fin n) : aeval x (r i) = 0 := by
    have h := congrFun hx i
    change (∑ j, algebraMap R K (a i j) * x j ^ p) - x i = algebraMap R K (b i) at h
    simp only [r, map_sub, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mp h).symm
  have hI : Ideal.span (Set.range r) ≤ RingHom.ker (aeval x).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  exact ⟨Ideal.Quotient.liftₐ _ (aeval x) (fun f hf ↦ hI hf)⟩

end Algebra
