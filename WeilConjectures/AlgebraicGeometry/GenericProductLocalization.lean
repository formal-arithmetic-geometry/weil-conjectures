/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

import WeilConjectures.AlgebraicGeometry.GenericProductMapDenominators
import WeilConjectures.AlgebraicGeometry.GenericProductKernelBound
import WeilConjectures.AlgebraicGeometry.GenericProductIdempotentBound

/-!
# GenericProductLocalization
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- A generic reduced product acquires an injective map and its coordinate idempotents
on a principal localization of the model ring. Any further principal localization retains
these properties. This statement does not descend the model to the original base. -/
theorem exists_generic_product_localization
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (R0 : Type (max u v)) [CommRing R0] [IsNoetherianRing R0] [IsDomain R0]
    [Algebra A R0] [Algebra R0 K'] [IsScalarTower A R0 K'] [IsFractionRing R0 K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (hsplit :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      Nonempty ((((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j))) :
    ∃ t : R0, t ≠ 0 ∧ ∀ (s : R0), t ∣ s →
      ∀ (R : Type u) [CommRing R] [Algebra R0 R] [IsLocalization.Away s R]
        [Algebra A R] [IsScalarTower A R0 R] [Algebra R K']
        [IsScalarTower R0 R K'] [IsFractionRing R K'],
        ∃ (_ : ∀ j, Algebra R (L j)) (_ : ∀ j, IsScalarTower R K' (L j)),
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
          ∃ f : ((B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)) →ₐ[R] (∀ j, L j),
            Function.Injective f ∧
            (∀ j, ∃ e, ∀ i, f e i = if i = j then 1 else 0) ∧
            (∀ j (z : L j), ∃ a : R, a ≠ 0 ∧
              ∃ x, algebraMap R (L j) a * z = f x j) := by
  classical
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
  obtain ⟨e⟩ := hsplit
  obtain ⟨tk, htk, hk⟩ := exists_generic_product_kernel_bound A B K K' R0 r L e
  obtain ⟨ti, hti, hi⟩ := exists_generic_product_idempotent_bound A B K K' R0 r L e
  refine ⟨tk * ti, mul_ne_zero htk hti, ?_⟩
  intro s hs R _ _ _ _ _ _ _ _
  let factors : ∀ j, Algebra R (L j) :=
    fun j ↦ Algebra.compHom (L j) (algebraMap R K')
  let towers : ∀ j, IsScalarTower R K' (L j) :=
    fun j ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A R K' := IsScalarTower.to₁₃₄ A R0 R K'
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
  obtain ⟨f, hcompat, hden⟩ := exists_generic_product_map_denominators A B K K' r L e R
  have hks : tk ∣ s := (dvd_mul_right tk ti).trans hs
  have his : ti ∣ s := (dvd_mul_left ti tk).trans hs
  exact ⟨factors, towers, f, hk s hks R f hcompat, hi s his R f hcompat, hden⟩
