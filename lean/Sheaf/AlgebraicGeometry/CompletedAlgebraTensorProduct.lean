/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Completed tensor products of adic algebras

Source: Stacks Project, Tags 0AHY, 0AHZ and 01I4, finite-quotient pushouts
(blueprint: def-per-completed-algebra-tensor-product).

The commutative ring pushout is the commutative algebra tensor product. Thus each term is
(R/K^n R) tensor (B/K^n B) over A/K^n, including its ring multiplication.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The coefficient homomorphism on power quotients.
Source: Stacks Tags 0AHY, 01I4 (blueprint: def-per-completed-algebra-tensor-product). -/
def adicPowerQuotientMap {A R : CommRingCat.{u}} (K : Ideal A) (f : A ⟶ R) (n : ℕ) :
    CommRingCat.of (A ⧸ K ^ n) ⟶ CommRingCat.of (R ⧸ (K.map f.hom) ^ n) :=
  CommRingCat.ofHom (Ideal.quotientMap _ f.hom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]))

/-- The finite quotient tensor product over the quotient of the base ring, as a ring pushout.
Source: Stacks Tag 01I4 (blueprint: def-per-completed-algebra-tensor-product). -/
noncomputable def adicQuotientTensor {A R B : CommRingCat.{u}} (K : Ideal A)
    (f : A ⟶ R) (g : A ⟶ B) (n : ℕ) : CommRingCat.{u} :=
  pushout (adicPowerQuotientMap K f n) (adicPowerQuotientMap K g n)

/-- The quotient transition between successive finite tensor products.
Source: Stacks Tags 0AHY, 01I4 (blueprint: def-per-completed-algebra-tensor-product). -/
noncomputable def adicQuotientTensorTransition {A R B : CommRingCat.{u}} (K : Ideal A)
    (f : A ⟶ R) (g : A ⟶ B) (n : ℕ) :
    adicQuotientTensor K f g (n + 2) ⟶ adicQuotientTensor K f g (n + 1) :=
  pushout.map (adicPowerQuotientMap K f (n + 2)) (adicPowerQuotientMap K g (n + 2))
    (adicPowerQuotientMap K f (n + 1)) (adicPowerQuotientMap K g (n + 1))
    (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ _))))
    (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ _))))
    (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ _))))
    (by ext x; rfl)
    (by ext x; rfl)

/-- The positive-power inverse system of commutative algebra tensor products.
Source: Stacks Tags 0AHY, 01I4 (blueprint: def-per-completed-algebra-tensor-product). -/
noncomputable def adicQuotientTensorTower {A R B : CommRingCat.{u}} (K : Ideal A)
    (f : A ⟶ R) (g : A ⟶ B) : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  Functor.ofOpSequence (X := fun n ↦ adicQuotientTensor K f g (n + 1))
    (adicQuotientTensorTransition K f g)

/-- The completed tensor product, constructed as compatible positive quotient tensors.
Source: Stacks Tags 0AHY, 01I4 (blueprint: def-per-completed-algebra-tensor-product). -/
noncomputable def adicCompletedAlgebraTensor {A R B : CommRingCat.{u}} (K : Ideal A)
    (f : A ⟶ R) (g : A ⟶ B) : CommRingCat.{u} :=
  limit (adicQuotientTensorTower K f g)

end AlgebraicGeometry
