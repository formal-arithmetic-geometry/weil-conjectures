/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Invariant expansion coefficients in a twisted tensor product

Source: Stacks Project, Tag 03C8 (`groupoids-lemma-basis`), second diagram,
left vertical basis isomorphism and coefficientwise equalizer comparison
(blueprint: lem-a1-twisted-tensor-invariant-coefficients).

The helpers instantiate Mathlib's tensor product and its canonical inclusions with
separate algebra structures on the two copies of the same ring.
-/

@[expose] public section

universe u v

namespace RingHom

/-- Mathlib's tensor product with the first scalar action through `σ` and the second
through `τ`. Source: Stacks Project, Tag 03C8, the ring `B ⊗[σ,A,τ] B`
(blueprint: lem-a1-twisted-tensor-invariant-coefficients). -/
def TwistedTensorProduct {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ τ : A →+* B) : Type v :=
  @TensorProduct A _ B B _ _ σ.toAlgebra.toModule τ.toAlgebra.toModule

/-- The tensor-product ring structure, instantiated from Mathlib with the two given
scalar actions. Source: Stacks Project, Tag 03C8
(blueprint: lem-a1-twisted-tensor-invariant-coefficients). -/
instance instCommRingTwistedTensorProduct {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (σ τ : A →+* B) : CommRing (TwistedTensorProduct σ τ) :=
  @Algebra.TensorProduct.instCommRing A B B _ _ σ.toAlgebra _ τ.toAlgebra

/-- The canonical ring map `p₀(b) = b ⊗ 1` into the twisted tensor product.
Source: Stacks Project, Tag 03C8
(blueprint: lem-a1-twisted-tensor-invariant-coefficients). -/
def twistedTensorLeft {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ τ : A →+* B) : B →+* TwistedTensorProduct σ τ :=
  @Algebra.TensorProduct.includeLeftRingHom A B B _ _ σ.toAlgebra _ τ.toAlgebra

/-- The canonical ring map `p₁(b) = 1 ⊗ b` into the twisted tensor product.
Source: Stacks Project, Tag 03C8
(blueprint: lem-a1-twisted-tensor-invariant-coefficients). -/
def twistedTensorRight {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ τ : A →+* B) : B →+* TwistedTensorProduct σ τ :=
  @AlgHom.toRingHom A B (TwistedTensorProduct σ τ) _ _ _ τ.toAlgebra
    (@Algebra.TensorProduct.instAlgebra A B B _ _ σ.toAlgebra _ τ.toAlgebra)
    (@Algebra.TensorProduct.includeRight A B B _ _ σ.toAlgebra _ τ.toAlgebra)

/-- The vectors `p₀(τ(x j))` form a basis over the second copy of `B`; the coefficients
of every expansion of `τ(a)` in the original basis are equalized by `σ` and `τ`.
Source: Stacks Project, Tag 03C8, second diagram, left vertical isomorphism and
coefficientwise equalizer comparison
(blueprint: lem-a1-twisted-tensor-invariant-coefficients).

Proof plan:
1. Base change the assumed `σ`-linear basis `τ(x j)` along `τ`. The right-tensor
   form of lem-weil-pbc-free-module-base-change-free gives the basis
   `E j = p₀(τ(x j))`, with scalars acting through `p₁`.
2. Fix an expansion `τ(a) = ∑ j, σ(c j) * τ(x j)`. The balancing relation of
   def-weil-pbc-module-tensor-product gives `p₀(σ(u)) = p₁(τ(u))`.
   The tensor ring structure and ring inclusions are supplied by
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Applying `Δ` and the
   assumed identities gives `p₀(τ(a)) = ∑ j, p₁(σ(c j)) * E j`.
   Applying `p₀` and balancing gives
   `p₀(τ(a)) = ∑ j, p₁(τ(c j)) * E j`.
3. Uniqueness of coefficients in the base-changed basis
   (def-weil-pbc-free-module) equates the two vectors of coefficients in `B`.
   Thus `σ(c j) = τ(c j)` for every `j`, for every `a`. -/
theorem twistedTensor_invariant_coefficients
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (σ τ : A →+* B)
    (Δ : B →+* TwistedTensorProduct σ τ)
    (_hΔσ : Δ.comp σ = (twistedTensorRight σ τ).comp σ)
    (_hΔτ : Δ.comp τ = (twistedTensorLeft σ τ).comp τ)
    (r : ℕ) (_hr : 1 ≤ r) (x : Fin r → A)
    (_hbasis : ∀ b : B, ∃! c : Fin r → A, b = ∑ j : Fin r, σ (c j) * τ (x j)) :
    (∃ e : @Module.Basis (Fin r) B (TwistedTensorProduct σ τ) _ _
        (twistedTensorRight σ τ).toAlgebra.toModule,
      ∀ j : Fin r, e j = twistedTensorLeft σ τ (τ (x j))) ∧
    ∀ (a : A) (c : Fin r → A),
      τ a = ∑ j : Fin r, σ (c j) * τ (x j) → ∀ j : Fin r, σ (c j) = τ (c j) := by
  sorry

end RingHom
