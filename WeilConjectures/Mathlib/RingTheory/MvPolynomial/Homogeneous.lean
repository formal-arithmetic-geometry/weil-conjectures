/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The degree-zero part of the total-degree grading on `MvPolynomial`

For the total-degree grading `MvPolynomial.gradedAlgebra` on `MvPolynomial σ R`, the
degree-zero part is the ring of constants. We record the resulting ring isomorphism and, for
a finite index type, that `MvPolynomial σ R` is of finite type over its degree-zero part.

## Main definitions

- `MvPolynomial.homogeneousSubmoduleZeroEquiv` — the isomorphism
  `R ≃+* MvPolynomial.homogeneousSubmodule σ R 0`, given by `r ↦ C r`.

## Main results

- `MvPolynomial.instFiniteTypeHomogeneousSubmoduleZero` — for `Finite σ`, the ring
  `MvPolynomial σ R` is of finite type over `MvPolynomial.homogeneousSubmodule σ R 0`.

## Implementation notes

The total-degree grading is not a global instance in Mathlib, since one may want to grade
`MvPolynomial σ R` by another weight function, so it is enabled locally here.
-/

@[expose] public section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type*) (R : Type*) [CommRing R]

/-- The base ring is isomorphic to the degree-zero piece of `R[X]` for the total-degree
grading, via `r ↦ C r`. -/
noncomputable def homogeneousSubmoduleZeroEquiv : R ≃+* homogeneousSubmodule σ R 0 where
  toFun r := ⟨C r, isHomogeneous_C σ r⟩
  invFun p := coeff 0 (p : MvPolynomial σ R)
  left_inv r := by simp
  right_inv p := Subtype.ext
    (totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr p.2)).symm
  map_mul' r s := Subtype.ext (by simp)
  map_add' r s := Subtype.ext (by simp)

@[simp]
lemma coe_homogeneousSubmoduleZeroEquiv (r : R) :
    (homogeneousSubmoduleZeroEquiv σ R r : MvPolynomial σ R) = C r :=
  rfl

/-- For a finite index type, `R[X]` is generated over the degree-zero part of the
total-degree grading by the variables. -/
instance [Finite σ] : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) := by
  classical
  cases nonempty_fintype σ
  refine ⟨⟨Finset.univ.image (X : σ → MvPolynomial σ R), eq_top_iff.mpr ?_⟩⟩
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (homogeneousSubmoduleZeroEquiv σ R r)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin (by simp))

end MvPolynomial
