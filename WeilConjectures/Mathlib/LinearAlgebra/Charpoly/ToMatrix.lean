/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Dual
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The reverse characteristic polynomial of an endomorphism

## Main declarations

* `LinearMap.charpolyRev`: the reverse characteristic polynomial `det (1 - t • f)` of an
  endomorphism `f` of a finite free module.
* `LinearMap.eval_charpolyRev`, `LinearMap.coeff_zero_charpolyRev`: the reverse characteristic
  polynomial takes the value `1` at `t = 0`, equivalently its constant coefficient is `1`.
* `LinearMap.natDegree_charpolyRev`, `LinearMap.leadingCoeff_charpolyRev`: for an endomorphism
  with invertible determinant, the reverse characteristic polynomial has full degree
  `finrank K V` and leading coefficient `(-1) ^ finrank K V * det f`.
* `LinearMap.natDegree_map_charpolyRev`: the degree is unchanged by mapping the coefficients
  along a ring homomorphism out of a field.
* `LinearMap.charpoly_dualMap`: the characteristic polynomial is invariant under transposition.
* `LinearMap.C_det_mul_charpolyRev`: if `f * g = c • 1`, then `det (1 - t • g)` is determined by
  the characteristic polynomial of `f`.
-/

@[expose] public section

open Module Polynomial

namespace LinearMap

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The reverse characteristic polynomial `det (1 - t • f)` of an endomorphism `f` of a finite
free module, defined as the reverse of the characteristic polynomial. -/
noncomputable def charpolyRev (f : M →ₗ[R] M) : R[X] := f.charpoly.reverse

theorem charpolyRev_def (f : M →ₗ[R] M) : f.charpolyRev = f.charpoly.reverse := rfl

theorem charpolyRev_toMatrix {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Basis ι R M)
    (f : M →ₗ[R] M) : (toMatrix b b f).charpolyRev = f.charpolyRev := by
  rw [charpolyRev_def, ← charpoly_toMatrix f b, Matrix.reverse_charpoly]

/-- The reverse characteristic polynomial `det (1 - t • f)` takes the value `1` at `t = 0`. -/
@[simp]
theorem eval_charpolyRev (f : M →ₗ[R] M) : Polynomial.eval 0 f.charpolyRev = 1 := by
  classical
  rw [← charpolyRev_toMatrix (Module.Free.chooseBasis R M) f, Matrix.eval_charpolyRev]

/-- The constant coefficient of the reverse characteristic polynomial `det (1 - t • f)` is `1`. -/
@[simp]
theorem coeff_zero_charpolyRev (f : M →ₗ[R] M) : f.charpolyRev.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_charpolyRev]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An endomorphism with invertible determinant has characteristic polynomial with nonzero
constant coefficient. -/
theorem charpoly_coeff_zero_ne_zero {f : V →ₗ[K] V} (hf : IsUnit (LinearMap.det f)) :
    f.charpoly.coeff 0 ≠ 0 := by
  intro h
  rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero] at hf
  exact not_isUnit_zero hf

/-- For an endomorphism with invertible determinant, the reverse characteristic polynomial
`det (1 - t • f)` has full degree `finrank K V`. -/
theorem natDegree_charpolyRev {f : V →ₗ[K] V} (hf : IsUnit (LinearMap.det f)) :
    f.charpolyRev.natDegree = finrank K V := by
  rw [charpolyRev_def, reverse_natDegree, charpoly_natDegree,
    natTrailingDegree_eq_zero.2 (Or.inr (charpoly_coeff_zero_ne_zero hf)), Nat.sub_zero]

/-- For an endomorphism with invertible determinant, the leading coefficient of the reverse
characteristic polynomial `det (1 - t • f)` is `(-1) ^ finrank K V * det f`. -/
theorem leadingCoeff_charpolyRev {f : V →ₗ[K] V} (hf : IsUnit (LinearMap.det f)) :
    f.charpolyRev.leadingCoeff = (-1) ^ finrank K V * LinearMap.det f := by
  rw [charpolyRev_def, reverse_leadingCoeff, trailingCoeff,
    natTrailingDegree_eq_zero.2 (Or.inr (charpoly_coeff_zero_ne_zero hf)),
    LinearMap.det_eq_sign_charpoly_coeff, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]

/-- Mapping the coefficients along a ring homomorphism out of a field preserves the degree of
the reverse characteristic polynomial. -/
theorem natDegree_map_charpolyRev {f : V →ₗ[K] V} (hf : IsUnit (LinearMap.det f))
    {S : Type*} [CommRing S] [Nontrivial S] (φ : K →+* S) :
    (f.charpolyRev.map φ).natDegree = finrank K V := by
  rw [natDegree_map_eq_of_injective φ.injective, natDegree_charpolyRev hf]

/-- The characteristic polynomial of the transpose of an endomorphism agrees with the
characteristic polynomial of the endomorphism. -/
theorem charpoly_dualMap (f : V →ₗ[K] V) : f.dualMap.charpoly = f.charpoly := by
  classical
  set b := Module.finBasis K V with hb
  rw [← charpoly_toMatrix f b, ← charpoly_toMatrix f.dualMap b.dualBasis, LinearMap.dualMap_def,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

/-- If `f * g = c • 1`, then the reverse characteristic polynomial of `g` is determined by the
characteristic polynomial of `f`. -/
theorem C_det_mul_charpolyRev {f g : V →ₗ[K] V} {c : K} (h : f * g = c • 1) :
    C f.det * g.charpolyRev = C ((-1) ^ finrank K V) * f.charpoly.comp (C c * X) := by
  classical
  set b := Module.finBasis K V with hb
  have hmul : toMatrix b b f * toMatrix b b g = c • 1 := by
    rw [← toMatrix_mul, h]
    simp
  have := Matrix.C_det_mul_charpolyRev hmul
  rwa [charpolyRev_toMatrix, charpoly_toMatrix, det_toMatrix, Fintype.card_fin] at this

end LinearMap
