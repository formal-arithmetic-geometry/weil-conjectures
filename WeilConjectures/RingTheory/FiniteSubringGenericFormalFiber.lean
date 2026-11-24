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

If a domain `A` is finite over a Noetherian subring `A0`, geometric regularity of generic
formal fibres ascends from `A0` to `A`.

## References

* Stacks Project, More on Algebra, Proposition 07PS, second paragraph, and Lemma 07PP(1).
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
