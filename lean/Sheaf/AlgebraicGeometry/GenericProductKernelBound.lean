/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas


/-! # GenericProductKernelBound

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- After one principal localization, every reduced generic product map compatible
with the fixed generic splitting is injective, including after further localization.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-kernel-bound)

Proof: Put C = (B tensor_A R0)_red. It is a finite R0-module. Tensor
associativity identifies its generic localization with the source of e: reduction
commutes with localization, since a fraction is nilpotent if and only if a denominator
multiple of its numerator is nilpotent. The kernel of the map from C to its generic
localization is torsion and finitely generated, since R0 is Noetherian. Choose a
nonzero annihilator for each generator and take their product t (1 for no generators).
Localizing at any s divisible by t kills the kernel. Localization is exact, so the
induced map from the localized C to the generic product is injective. Reduction
commutes with this principal localization and identifies its source with
(B tensor_A R)_red. The pure-tensor compatibility determines the map f uniquely:
R-linearity determines all pure tensors and additivity determines their sums; the
quotient map is surjective. Thus f is the injective induced map. When the generic
product is zero, the kernel is all of C and the same torsion argument kills C. -/
theorem exists_generic_product_kernel_bound
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (R0 : Type (max u v)) [CommRing R0] [IsNoetherianRing R0]
    [IsDomain R0]
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
          Function.Injective f := by sorry
