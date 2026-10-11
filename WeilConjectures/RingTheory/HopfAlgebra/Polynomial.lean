/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# The Hopf algebra `R[X]` with `X` primitive

The polynomial ring `R[X]` over a commutative ring `R` is a commutative and cocommutative Hopf
algebra in which the variable is primitive: the comultiplication, counit and antipode are the
`R`-algebra homomorphisms with `Δ(X) = X ⊗ 1 + 1 ⊗ X`, `ε(X) = 0` and `S(X) = -X`. This is the
coordinate ring of the additive group `𝔾ₐ = Spec R[X]`: the three structure maps are dual to the
addition `(x, y) ↦ x + y`, the zero `0` and the negation `x ↦ -x`.

This is the special case `M = R` of the bialgebra structure `SymmetricAlgebra.instBialgebra` on
the symmetric algebra, in which every generator is primitive.

## Main definitions

- `Polynomial.instBialgebra`: the bialgebra structure on `R[X]` with `X` primitive.
- `Polynomial.instHopfAlgebra`: the Hopf algebra structure on `R[X]`, with antipode `X ↦ -X`.
- `Polynomial.algHomMulEquiv`: `R`-algebra homomorphisms `R[X] → S`, with the convolution
  product, are the additive group of `S`: the `S`-points of `𝔾ₐ` are `S`.

## Main results

- `Polynomial.comul_X_pow_char`: in characteristic `p`, `X ^ p` is primitive, so that
  `(X ^ p)` is a Hopf ideal (`Polynomial.isHopfIdeal_span_X_pow_char`), cutting out `α_p`.

## Blueprint

- `def-sc-gm-ga`: the coordinate ring `k[y]` of the additive group `𝐆_a`, with
  `m^*(y) = y ⊗ 1 + 1 ⊗ y`, `ε(y) = 0` and `i^*(y) = -y`, and the Hopf ideal `(y^p)` of `α_p`.
-/

@[expose] public section

open TensorProduct

namespace Polynomial

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The bialgebra structure on `R[X]` in which `X` is primitive: `Δ(X) = X ⊗ 1 + 1 ⊗ X` and
`ε(X) = 0`. (blueprint: `def-sc-gm-ga`) -/
noncomputable instance instBialgebra : Bialgebra R R[X] :=
  .ofAlgHom (aeval (X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X)) (aeval 0)
    (by
      ext
      simp [Algebra.TensorProduct.one_def, add_tmul, tmul_add]
      abel)
    (by ext; simp)
    (by ext; simp)

variable {R}

@[simp]
theorem comul_X : Coalgebra.comul (R := R) (X : R[X]) = X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X :=
  aeval_X _

@[simp]
theorem counit_X : Coalgebra.counit (R := R) (X : R[X]) = 0 :=
  aeval_X _

@[simp]
theorem comulAlgHom_X : Bialgebra.comulAlgHom R R[X] X = X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] X :=
  comul_X

@[simp]
theorem counitAlgHom_X : Bialgebra.counitAlgHom R R[X] X = 0 :=
  counit_X

instance instIsCocomm : Coalgebra.IsCocomm R R[X] where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R R[X] R[X]).toAlgHom.comp
        (Bialgebra.comulAlgHom R R[X]) = Bialgebra.comulAlgHom R R[X] := by
      ext
      simp [add_comm]
    exact congr(($h).toLinearMap)

variable (R) (S : Type*) [CommSemiring S] [Algebra R S]

/-- `R`-algebra homomorphisms `R[X] → S`, with the convolution product, are the additive group of
`S`: a homomorphism `φ` corresponds to `φ(X)`. In other words, the `S`-points of
`𝔾ₐ = Spec R[X]` are the group `S` (written multiplicatively). -/
noncomputable def algHomMulEquiv : WithConv (R[X] →ₐ[R] S) ≃* Multiplicative S where
  toFun φ := .ofAdd (φ.ofConv X)
  invFun s := WithConv.toConv (aeval s.toAdd)
  left_inv φ := by
    ext1
    ext
    simp
  right_inv s := by simp
  map_mul' φ ψ := by simp [AlgHom.convMul_apply, ← ofAdd_add]

variable {R S}

@[simp]
theorem toAdd_algHomMulEquiv (φ : WithConv (R[X] →ₐ[R] S)) :
    (algHomMulEquiv R S φ).toAdd = φ.ofConv X :=
  rfl

@[simp]
theorem algHomMulEquiv_symm_apply (s : Multiplicative S) :
    (algHomMulEquiv R S).symm s = WithConv.toConv (aeval s.toAdd) :=
  rfl

/-- In characteristic `p`, the `p`-th power of the primitive element `X` is primitive. -/
theorem comul_X_pow_char (p : ℕ) [hp : Fact p.Prime] [CharP R p] :
    Coalgebra.comul (R := R) (X ^ p : R[X]) = (X ^ p) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (X ^ p) := by
  have h0 : (p : R[X] ⊗[R] R[X]) = 0 := by
    rw [← map_natCast (algebraMap R (R[X] ⊗[R] R[X])), CharP.cast_eq_zero, map_zero]
  rw [← Bialgebra.comulAlgHom_apply, map_pow, comulAlgHom_X, add_pow_prime_eq hp.out, h0,
    zero_mul, zero_mul, zero_mul, add_zero, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_pow, one_pow]

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- The Hopf algebra structure on `R[X]` with `X` primitive: the antipode is `X ↦ -X`.
(blueprint: `def-sc-gm-ga`) -/
noncomputable instance instHopfAlgebra : HopfAlgebra R R[X] :=
  .ofAlgHom (aeval (-X)) (by ext; simp) (by ext; simp)

variable {R}

@[simp]
theorem antipode_X : HopfAlgebra.antipode R (X : R[X]) = -X :=
  aeval_X _

/-- In characteristic `p`, the ideal `(X ^ p)` of `R[X]` is a Hopf ideal: it cuts out the Frobenius
kernel `α_p` of `𝔾ₐ`. (blueprint: `def-sc-gm-ga`) -/
instance isHopfIdeal_span_X_pow_char (p : ℕ) [hp : Fact p.Prime] [CharP R p] :
    (Ideal.span {(X ^ p : R[X])}).IsHopfIdeal R :=
  Ideal.isHopfIdeal_span_singleton_of_comul_eq
    (by rw [← Bialgebra.counitAlgHom_apply, map_pow, counitAlgHom_X, zero_pow hp.out.ne_zero])
    (comul_X_pow_char p)

end CommRing

end Polynomial
