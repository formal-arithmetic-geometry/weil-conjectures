/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # GenericProductMapDenominators

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- A generic splitting defines the reduced base-change map, with coordinate denominator
clearing and a specified value on the image of every element of the original algebra.
Neither finiteness nor Noetherianity is needed for this assertion.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-map-denominators)

Proof: Tensor associativity and commutation identify B tensor_A K' with
(K tensor_A B) tensor_K K'. The map B tensor_A R to this generic algebra followed
by the quotient and e kills every nilpotent, because a product of fields is reduced.
Thus it factors through the source reduction, giving f and the pure-tensor identity.
For z in L_j, apply e inverse to the vector supported at j with value z. Every element
of B tensor_A K' is a finite sum of pure tensors. Write their K' coefficients as
fractions over R, multiply the finitely many nonzero denominators, and lift the
resulting numerator to B tensor_A R. Passing to the quotient gives a*z = f(x)_j.
The product denominator is nonzero: R embeds in its fraction field K'. Empty sums
use denominator 1. If r is zero the coordinate assertion is vacuous. -/
theorem exists_generic_product_map_denominators
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (K : Type u) [Field K] [Algebra A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (e :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      (((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j))
    (R : Type u) [CommRing R] [Algebra A R] [Algebra R K']
    [IsScalarTower A R K'] [IsFractionRing R K']
    [∀ j, Algebra R (L j)] [∀ j, IsScalarTower R K' (L j)] :
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
    ∃ f : ((B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)) →ₐ[R] (∀ j, L j),
            (∀ b : B, f (Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : R))) =
              e (Ideal.Quotient.mk _ (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')))) ∧
            (∀ j (z : L j), ∃ a : R, a ≠ 0 ∧
              ∃ x, algebraMap R (L j) a * z = f x j) := by sorry
