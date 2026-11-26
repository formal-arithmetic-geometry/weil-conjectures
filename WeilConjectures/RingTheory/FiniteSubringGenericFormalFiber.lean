/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.FormalFibreQuasiFiniteAscent
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.GenericFormalFiberFiniteSubringBase
import WeilConjectures.RingTheory.GenericFormalFiberFractionFieldTransport

/-!
# Generic formal fibres and finite subrings

Geometric regularity of the generic formal fibre ascends from a finite Noetherian subring of a
Noetherian domain.

## Main results

* `isGeometricallyRegular_genericFormalFiber_of_finite_subring`

## Implementation details

The inclusion `A₀ → A` is finite, hence quasi-finite at every prime, so Tag 07PP(1) applies to
the zero primes. The residue field of the zero prime of `A` is then identified with the chosen
fraction field `K`, and the generic fibres are identified accordingly.

## References

* [Stacks, Tag 07PS] (second paragraph)
* [Stacks, Tag 07PP] (part (1))
-/

@[expose] public section

universe u

/-- Geometric regularity of the generic formal fibre ascends from a finite Noetherian
subring of a domain, with any chosen fraction field for the resulting fibre. -/
theorem isGeometricallyRegular_genericFormalFiber_of_finite_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (A₀ : Subring A) [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (P : Ideal A) [P.IsPrime]
    (hbase :
      let P₀ := P.comap (algebraMap A₀ A)
      let C₀ := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P₀))
        (Localization.AtPrime P₀)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A₀).ResidueField
        ((⊥ : Ideal A₀).Fiber C₀)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  apply genericFormalFiber_geometricallyRegular_of_fractionField_transport A K P
  exact genericFormalFiber_bot_geometricallyRegular_of_finite_subring A A₀ P hbase
