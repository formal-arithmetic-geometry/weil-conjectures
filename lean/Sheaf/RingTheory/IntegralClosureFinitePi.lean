/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closure in finite products of ring maps

Source: Stacks Project, Algebra, Tags 0CY8 and 0CY9
(blueprint: lem-weil-pbc-finite-product-integral-closure).
-/

@[expose] public section

universe w u v

/-- The integral closure of a finite product of ring maps is the product of the component
integral closures. For injective component maps, the product is integrally closed if and only
if every component is integrally closed. Source: Stacks Project, Algebra, Tag 0CY9, using 0CY8
(blueprint: lem-weil-pbc-finite-product-integral-closure).

Proof: project a monic polynomial annihilating a tuple to each coordinate to prove that its
coordinates are integral (def-weil-pbc-integral-closure). Conversely, choose monic annihilating
polynomials in each coordinate. Finiteness permits a common degree D at least one; multiply
each polynomial of degree d by T^(D-d), and assemble the coefficients coordinatewise. This
produces a monic polynomial over the product ring annihilating the tuple. For the empty
product both rings are zero rings and T suffices. The coordinatewise integrality criterion
identifies the integral-closure subring with the intersection of the inverse images of the
component closures under evaluation. If the component maps are injective, their product is
injective, and this equality identifies the closure with the base ring exactly when every
component closure equals its base ring, also for the empty product. -/
theorem integralClosure_finite_pi {I : Type w} [Finite I]
    (R : I → Type u) (S : I → Type v) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (φ : ∀ i, R i →+* S i) :
    letI : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra
    (integralClosure (∀ i, R i) (∀ i, S i)).toSubring =
        ⨅ i, (integralClosure (R i) (S i)).toSubring.comap (Pi.evalRingHom S i) ∧
      ((∀ i, Function.Injective (φ i)) →
        (IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
          ∀ i, IsIntegrallyClosedIn (R i) (S i))) := by
  sorry
