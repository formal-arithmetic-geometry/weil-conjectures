/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization of a reduced tensor-product decomposition

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, step 9.
(blueprint: lem-weil-pbc-reduced-product-localization)
-/

@[expose] public section

set_option autoImplicit false
universe u v
open scoped TensorProduct

/-- Source: smooth purity blueprint, sk-prop-sf-cbc,
lem-weil-pbc-finite-pushforward-generic-constructible, step 9.
(blueprint: lem-weil-pbc-reduced-product-localization)

Proof: C' is the localization of C at x. Therefore B tensor_R C' is the
localization of B tensor_R C at the image of x, by the tensor associativity
isomorphism and the universal property of localization. The nilradical of a
localization is the extension of the nilradical: if a fraction is nilpotent,
a power of its numerator is killed by a power of the denominator; multiplying
the numerator by a sufficiently large denominator power gives a nilpotent
numerator for the same fraction. The reverse inclusion is immediate.
Consequently reduction commutes with this localization. Localize the given
C-algebra equivalence. Localization commutes with the finite product over Fin r,
since denominators of finitely many components have a common power. Each factor
localization is C' tensor_C D_j. Composing these identifications gives the
asserted C'-algebra equivalence. For r=0 both finite products are the zero ring.
No finiteness, domain, etaleness or universal-homeomorphism hypothesis is needed. -/
theorem reduced_product_localization
    (R : Type u) [CommRing R]
    (B : Type v) [CommRing B] [Algebra R B]
    (C : Type u) [CommRing C] [Algebra R C]
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra C (D j)]
    (hsplit : letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C)
      Nonempty (((B ⊗[R] C) ⧸ nilradical (B ⊗[R] C)) ≃ₐ[C] (∀ j, D j)))
    (x : C) (C' : Type u) [CommRing C'] [Algebra C C'] [IsLocalization.Away x C']
    [Algebra R C'] [IsScalarTower R C C'] :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C')
    Nonempty (((B ⊗[R] C') ⧸ nilradical (B ⊗[R] C')) ≃ₐ[C']
      (∀ j, C' ⊗[C] D j)) := by
  sorry
