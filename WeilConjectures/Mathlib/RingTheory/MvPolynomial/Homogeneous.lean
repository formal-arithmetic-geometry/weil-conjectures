/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Complements on homogeneous multivariate polynomials

Facts about the total-degree grading of `MvPolynomial σ R` that are not in Mathlib. The
degree-zero part of this grading is the ring of constants; we record the resulting ring
isomorphism and, for a finite index type, that `MvPolynomial σ R` is of finite type over its
degree-zero part.

## Main definitions

- `MvPolynomial.homogeneousSubmoduleZeroEquiv` — the isomorphism
  `R ≃+* MvPolynomial.homogeneousSubmodule σ R 0`, given by `r ↦ C r`.

## Main results

- `MvPolynomial.IsHomogeneous.eval₂_const_mul` — evaluating a homogeneous polynomial of
  degree `n` at a scaled family of values scales the value by `c ^ n`.
- `MvPolynomial.instFiniteTypeHomogeneousSubmoduleZero` — for `Finite σ`, the ring
  `MvPolynomial σ R` is of finite type over `MvPolynomial.homogeneousSubmodule σ R 0`.

## Implementation notes

The total-degree grading is not a global instance in Mathlib, since one may want to grade
`MvPolynomial σ R` by another weight function, so it is enabled locally here.
-/

@[expose] public section

universe u

namespace MvPolynomial

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluating a polynomial that is homogeneous of degree `n` at `c • g` gives `c ^ n` times
its value at `g`. -/
theorem IsHomogeneous.eval₂_const_mul {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (f : R →+* S) (c : S) (g : σ → S) :
    _root_.MvPolynomial.eval₂ f (fun i ↦ c * g i) φ =
      c ^ n * _root_.MvPolynomial.eval₂ f g φ := by
  rw [_root_.MvPolynomial.eval₂_eq, _root_.MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [hφ.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

/-- The base ring is isomorphic to the degree-zero piece of `MvPolynomial σ R` for the
total-degree grading, via `r ↦ C r`. -/
noncomputable def homogeneousSubmoduleZeroEquiv : R ≃+* homogeneousSubmodule σ R 0 where
  toFun r := ⟨C r, isHomogeneous_C σ r⟩
  invFun p := coeff 0 (p : MvPolynomial σ R)
  left_inv r := by simp
  right_inv p := Subtype.ext <| by
    have h : (p : MvPolynomial σ R).totalDegree = 0 :=
      (totalDegree_zero_iff_isHomogeneous _).mpr p.2
    exact (totalDegree_eq_zero_iff_eq_C.mp h).symm
  map_mul' a b := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp]
lemma coe_homogeneousSubmoduleZeroEquiv (r : R) :
    (homogeneousSubmoduleZeroEquiv (σ := σ) r : MvPolynomial σ R) = C r :=
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a finite index type, `R[X]` is generated over the degree-zero part of the
total-degree grading by the variables. -/
instance [Finite σ] : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) := by
  classical
  cases nonempty_fintype σ
  refine ⟨⟨Finset.univ.image (X : σ → MvPolynomial σ R), eq_top_iff.mpr ?_⟩⟩
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (homogeneousSubmoduleZeroEquiv (σ := σ) (R := R) r)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin (by simp))

end MvPolynomial
