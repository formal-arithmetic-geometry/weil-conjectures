/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.GenericFormalFiberNoetherian
import WeilConjectures.RingTheory.GenericFormalFiberPurelyInseparableRegular

/-!
# Generic formal fibres of regular power-series models

The generic formal fibre of a regular local domain presented as a finite-variable power series
ring over a field or a Cohen ring is geometrically regular.

## Implementation details

The completion of the localization at `P` is regular local (Tag 07NY), hence regular (Tag 0AFS),
and the generic fibre is a localization of it. In characteristic zero, finite purely inseparable
extensions are trivial. In positive characteristic the Cohen-ring case is impossible, since a
Cohen ring has characteristic zero, so `A ≅ k[[X_1, …, X_d]]` and Tag 07PR (with no polynomial
variables) applies after transporting along the induced isomorphisms.

## References

* [Stacks, Tag 07PS] (last two paragraphs)
* [Stacks, Tags 0AFS, 07NY, 07PR]
-/

@[expose] public section

universe u

/-- The generic formal fibre of a regular local domain presented as a finite-variable
power series ring over a field or a Cohen ring is geometrically regular. -/
theorem isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (hmodel :
      (∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
        let _ := h
        Nonempty (A ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
        let _ := h
        ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (A ≃+* MvPowerSeries (Fin d) Λ)))
    (P : Ideal A) [P.IsPrime] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C) := by
  dsimp [Algebra.IsGeometricallyRegular]
  constructor
  · exact isNoetherian_genericFormalFiber_of_regular_powerSeries A hmodel P
  · exact isRegular_genericFormalFiber_after_finite_purelyInseparable A hmodel P
