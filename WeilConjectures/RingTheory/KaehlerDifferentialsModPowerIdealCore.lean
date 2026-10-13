/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.TensorProduct.Tower
@[expose] public section
open scoped TensorProduct
universe u v
/-- The canonical map on Kähler differentials modulo a power of an ideal is bijective.
This is the exactness and Leibniz argument of Stacks Tag 02HQ; the map is uniquely
specified on tensor generators by the displayed formula.

Proof: tensor the conormal exact sequence for the quotient with S/I^n, identify the
middle tensor by cancellation, and use the Leibniz rule to show the kernel generators
vanish.
(blueprint: lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective) -/
theorem kahlerDifferential_mod_power_ideal_bijective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (n : ℕ) (_hn : 1 ≤ n) :
    letI : Algebra (S ⧸ I ^ (n + 1)) (S ⧸ I ^ n) :=
      (Ideal.Quotient.factorPowSucc I n).toAlgebra
    ∃ f : (S ⧸ I ^ n) ⊗[S] KaehlerDifferential R S →ₗ[S ⧸ I ^ n]
        (S ⧸ I ^ n) ⊗[S ⧸ I ^ (n + 1)]
          KaehlerDifferential R (S ⧸ I ^ (n + 1)),
      Function.Bijective f ∧
      ∀ (s t : S),
        f (Ideal.Quotient.mk (I ^ n) t ⊗ₜ[S] KaehlerDifferential.D R S s) =
          Ideal.Quotient.mk (I ^ n) t ⊗ₜ[S ⧸ I ^ (n + 1)]
            KaehlerDifferential.D R (S ⧸ I ^ (n + 1))
              (Ideal.Quotient.mk (I ^ (n + 1)) s) := by
  sorry
