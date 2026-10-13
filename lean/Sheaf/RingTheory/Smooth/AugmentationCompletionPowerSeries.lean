/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Power-series coordinates on the completion of a smooth augmented algebra

Source: Stacks Project, Tag 05D5.
(blueprint: lem-sbc-smooth-augmentation-completion-power-series)
-/

@[expose] public section

universe u

namespace Algebra

/-- The augmentation-adic completion of a smooth algebra over a local ring has
power-series coordinates preserving the augmentation.

Source: Stacks Project, Tag 05D5, including its explicit choice of generators.
(blueprint: lem-sbc-smooth-augmentation-completion-power-series)

Proof: Put I = ker ε. The split conormal sequence identifies I/I² with
Ω[C/B] ⊗[C,ε] B, a finite projective B-module. Over the local ring it is free
of some finite rank n. Lift a basis to I. Sending the variables to these lifts
induces Ψ : B[[X₁,...,Xₙ]] → Ĉ. Modulo the squares of the two ideals Ψ is an
isomorphism. Inductively, formal smoothness lifts the inverse modulo the k-th
power to the next power. The resulting composite on truncated power series
sends Xᵢ to Xᵢ plus a term of degree at least k; subtracting these terms gives
its inverse. Surjectivity of Ψ on each truncation then makes the lifted map an
inverse of Ψ. These inverses are compatible, so inverse limits give an algebra
isomorphism. Take its inverse for e. Because the chosen lifts lie in I,
constant coefficient after e agrees with ε on C. Rank zero is allowed and
produces the constant power-series ring. -/
theorem exists_augmented_completion_powerSeries
    (B C : Type u) [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
    [Smooth B C] (ε : C →ₐ[B] B) :
    ∃ (n : ℕ) (e : AdicCompletion (RingHom.ker ε.toRingHom) C ≃ₐ[B]
        MvPowerSeries (Fin n) B),
      ∀ c : C, MvPowerSeries.constantCoeff
        (e (algebraMap C (AdicCompletion (RingHom.ker ε.toRingHom) C) c)) = ε c := by sorry

end Algebra
