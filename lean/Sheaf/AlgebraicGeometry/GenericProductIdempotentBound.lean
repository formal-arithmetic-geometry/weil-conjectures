/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # GenericProductIdempotentBound

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- After one principal localization, every reduced generic product map compatible
with the fixed splitting contains all the coordinate idempotents in its image.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-idempotent-bound)

Proof: Put C = (B tensor_A R0)_red. Tensor associativity and localization
of the nilradical identify its generic localization with the given product via e.
For each of the finitely many coordinate idempotents, choose a numerator in C and a
nonzero R0 denominator. Take t to be the product of these denominators. It is nonzero
because R0 is a domain. If t divides s, every denominator divides s, hence is a unit
in R0[1/s]. Map the chosen numerator to (B tensor_A R)_red and multiply it by the
inverse of the image of its denominator. Its image in the generic product is exactly
the desired coordinate idempotent. Compatibility on pure tensors, together with
R-linearity and surjectivity of the quotient, identifies any specified f with this
canonical map, so the construction works for every such f. For r = 0 choose t = 1;
there is no coordinate to lift. Neither injectivity nor Noetherianity is used. -/
theorem exists_generic_product_idempotent_bound
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (R0 : Type (max u v)) [CommRing R0] [IsDomain R0]
    [Algebra A R0] [Algebra R0 K'] [IsScalarTower A R0 K']
    [IsFractionRing R0 K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (e :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      (((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j))
    : ∃ t : R0, t ≠ 0 ∧ ∀ s : R0, t ∣ s →
      ∀ (R : Type u) [CommRing R] [Algebra R0 R] [IsLocalization.Away s R]
        [Algebra A R] [IsScalarTower A R0 R] [Algebra R K']
        [IsScalarTower R0 R K'] [IsFractionRing R K']
        [∀ j, Algebra R (L j)] [∀ j, IsScalarTower R K' (L j)],
        letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
        ∀ f : ((B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)) →ₐ[R] (∀ j, L j),
            (∀ b : B, f (Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : R))) =
              e (Ideal.Quotient.mk _ (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')))) →
          (∀ j, ∃ x, ∀ i, f x i = if i = j then 1 else 0) := by sorry
