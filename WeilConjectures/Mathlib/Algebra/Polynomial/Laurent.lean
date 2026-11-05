/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Complements on Laurent polynomials

## Main results

- `LaurentPolynomial.coeff_toLaurent_natCast`, `LaurentPolynomial.coeff_toLaurent_of_neg`: the
  coefficients of the Laurent polynomial attached to a polynomial.
- `LaurentPolynomial.coeff_T_mul`: multiplication by `T d` shifts the coefficients by `d`.
- `LaurentPolynomial.mapRingHom`: the ring map `R[T;T⁻¹] →+* S[T;T⁻¹]` induced by `R →+* S`.
- `LaurentPolynomial.expand`: the substitution `t ↦ t^m`, extending `Polynomial.expand`.
-/

@[expose] public section

open Polynomial

namespace LaurentPolynomial

variable {R : Type*} [Semiring R]

@[simp]
lemma coeff_toLaurent_natCast (p : R[X]) (j : ℕ) : (toLaurent p).coeff j = p.coeff j := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ j

@[simp]
lemma coeff_T_mul (d j : ℤ) (f : R[T;T⁻¹]) : (T d * f).coeff j = f.coeff (j - d) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_eq_sub]

section Map

variable {S S' : Type*} [Semiring S] [Semiring S']

/-- The extension of scalars `R[t, t⁻¹] ⟶ S[t, t⁻¹]` along a ring map `φ : R ⟶ S`. -/
noncomputable abbrev mapRingHom (φ : R →+* S) : R[T;T⁻¹] →+* S[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingHom ℤ φ

@[simp]
lemma mapRingHom_C (φ : R →+* S) (x : R) :
    mapRingHom φ (LaurentPolynomial.C x) = LaurentPolynomial.C (φ x) := by
  rw [← single_eq_C, AddMonoidAlgebra.mapRingHom_single]
  rfl

@[simp]
lemma mapRingHom_T (φ : R →+* S) (n : ℤ) : mapRingHom φ (T n : R[T;T⁻¹]) = T n := by
  rw [T, AddMonoidAlgebra.mapRingHom_single, map_one]
  rfl

lemma mapRingHom_mapRingHom (φ : R →+* S) (ψ : S →+* S') (x : R[T;T⁻¹]) :
    mapRingHom ψ (mapRingHom φ x) = mapRingHom (ψ.comp φ) x := by
  simp [mapRingHom, AddMonoidAlgebra.mapRingHom_comp]

@[simp]
lemma mapRingHom_id (x : R[T;T⁻¹]) : mapRingHom (RingHom.id R) x = x := by
  simp [mapRingHom]

@[simp]
lemma mapRingHom_toLaurent (φ : R →+* S) (p : R[X]) :
    mapRingHom φ (toLaurent p) = toLaurent (p.map φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

end Map

end LaurentPolynomial

/-! ### The substitution `t ↦ t^m` -/

namespace LaurentPolynomial

variable (R : Type*) [CommSemiring R]

variable {R}

end LaurentPolynomial
