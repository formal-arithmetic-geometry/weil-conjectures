/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.RingTheory.HopfAlgebra.HopfIdeal

/-!
# The Hopf algebra of the multiplicative group

The Laurent polynomial ring `k[T;T⁻¹]` is Mathlib's Hopf algebra `LaurentPolynomial.instHopfAlgebra`
(the group algebra of `ℤ`): the coordinate ring of the multiplicative group `𝔾ₘ`, with
`Δ(T) = T ⊗ T`, `ε(T) = 1` and `S(T) = T⁻¹`. A `k`-algebra homomorphism `k[T;T⁻¹] → R` is the
same as a unit of `R`, and the convolution product corresponds to multiplication of units
(`LaurentPolynomial.algHomMulEquiv`).

For `n : ℕ` the ideal `(T ^ n - 1)` is a Hopf ideal; it cuts out the group scheme `μ_n` of
`n`-th roots of unity.

## Main definitions

- `LaurentPolynomial.evalUnit`: evaluation of Laurent polynomials at a unit.
- `LaurentPolynomial.algHomMulEquiv`: `k`-algebra homomorphisms `k[T;T⁻¹] → R`, with the
  convolution product, are the units of `R`.
- `LaurentPolynomial.rootsOfUnityIdeal`: the Hopf ideal `(T ^ n - 1)` of `μ_n`.
-/

@[expose] public section

open TensorProduct

namespace LaurentPolynomial

variable {k : Type*} [CommRing k]

/-- Two `k`-algebra homomorphisms out of `k[T;T⁻¹]` agreeing on `T` are equal. -/
theorem algHom_ext_T {A : Type*} [Semiring A] [Algebra k A] {f g : k[T;T⁻¹] →ₐ[k] A}
    (h : f (T 1) = g (T 1)) : f = g := by
  have h' : f (T (-1)) = g (T (-1)) := by
    refine left_inv_eq_right_inv (a := f (T 1)) ?_ ?_
    · rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]
    · rw [h, ← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  refine AddMonoidAlgebra.algHom_ext (fun n ↦ ?_) (Subsingleton.elim _ _)
  change f (T n) = g (T n)
  induction n using Int.induction_on with
  | zero => rw [T_zero, map_one, map_one]
  | succ n ih => rw [T_add, map_mul, map_mul, ih, h]
  | pred n ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, h']

variable (k) {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation of Laurent polynomials at a unit `u` of a `k`-algebra `R`: the `k`-algebra
homomorphism `k[T;T⁻¹] → R` sending `T` to `u`. -/
noncomputable def evalUnit (u : Rˣ) : k[T;T⁻¹] →ₐ[k] R :=
  AddMonoidAlgebra.lift k R ℤ ((Units.coeHom R).comp (zpowersHom Rˣ u))

variable {k}

@[simp]
theorem evalUnit_T (u : Rˣ) (n : ℤ) : evalUnit k u (T n) = ((u ^ n : Rˣ) : R) := by
  simp [evalUnit, T, -single_eq_C_mul_T]

/-- The value at `T` of a `k`-algebra homomorphism out of `k[T;T⁻¹]`, as a unit. -/
noncomputable def unitOfAlgHom (φ : k[T;T⁻¹] →ₐ[k] R) : Rˣ where
  val := φ (T 1)
  inv := φ (T (-1))
  val_inv := by rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  inv_val := by rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]

@[simp]
theorem val_unitOfAlgHom (φ : k[T;T⁻¹] →ₐ[k] R) : (unitOfAlgHom φ : R) = φ (T 1) :=
  rfl

variable (k R)

/-- `k`-algebra homomorphisms `k[T;T⁻¹] → R`, with the convolution product, are the units of `R`:
a homomorphism corresponds to its value at `T`. -/
noncomputable def algHomMulEquiv : WithConv (k[T;T⁻¹] →ₐ[k] R) ≃* Rˣ where
  toFun φ := unitOfAlgHom φ.ofConv
  invFun u := WithConv.toConv (evalUnit k u)
  left_inv φ := by
    refine WithConv.ext (algHom_ext_T ?_)
    simp
  right_inv u := Units.ext (by simp)
  map_mul' φ ψ := Units.ext (by simp [AlgHom.convMul_apply])

variable {k R}

@[simp]
theorem val_algHomMulEquiv (φ : WithConv (k[T;T⁻¹] →ₐ[k] R)) :
    (algHomMulEquiv k R φ : R) = φ.ofConv (T 1) :=
  rfl

section RootsOfUnity

variable (k) (n : ℕ)

/-- The ideal `(T ^ n - 1)` of `k[T;T⁻¹]`. It is a Hopf ideal, cutting out the group scheme
`μ_n = Spec k[T;T⁻¹] ⧸ (T ^ n - 1) ≅ Spec k[T] ⧸ (T ^ n - 1)` of `n`-th roots of unity. -/
noncomputable def rootsOfUnityIdeal : Ideal k[T;T⁻¹] :=
  Ideal.span {T n - 1}

theorem T_sub_one_mem_rootsOfUnityIdeal : (T n - 1 : k[T;T⁻¹]) ∈ rootsOfUnityIdeal k n :=
  Ideal.subset_span rfl

/-- The ideal `(T ^ n - 1)` is a Hopf ideal of `k[T;T⁻¹]`. -/
instance isHopfIdeal_rootsOfUnityIdeal : (rootsOfUnityIdeal k n).IsHopfIdeal k := by
  refine Ideal.isHopfIdeal_span ?_ ?_ ?_ <;> rintro x rfl
  · rw [map_sub, counit_T, Bialgebra.counit_one, sub_self]
  · have h : Ideal.Quotient.mkₐ k (Ideal.span {(T n - 1 : k[T;T⁻¹])}) (T n) = 1 := by
      rw [← map_one (Ideal.Quotient.mkₐ k _), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      exact T_sub_one_mem_rootsOfUnityIdeal k n
    rw [map_sub, comul_T, Bialgebra.comul_one, map_sub, map_one, Algebra.TensorProduct.map_tmul,
      h, Algebra.TensorProduct.one_def, sub_self]
  · rw [map_sub, antipode_T, HopfAlgebra.antipode_one]
    have : (T (-(n : ℤ)) - 1 : k[T;T⁻¹]) = -T (-(n : ℤ)) * (T n - 1) := by
      rw [neg_mul, mul_sub, ← T_add, neg_add_cancel, T_zero, mul_one, neg_sub]
    rw [this]
    exact Ideal.mul_mem_left _ _ (T_sub_one_mem_rootsOfUnityIdeal k n)

end RootsOfUnity

end LaurentPolynomial
