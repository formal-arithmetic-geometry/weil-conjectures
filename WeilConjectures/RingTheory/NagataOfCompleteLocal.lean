/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import WeilConjectures.RingTheory.PowerSeriesN2
import WeilConjectures.RingTheory.TateN2CompletePrincipal
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Complete Noetherian local rings are Nagata

A Noetherian ring complete at its unique maximal ideal is Nagata.

## Implementation details

Each prime quotient is a complete Noetherian local domain, which is finite over a power series
ring over a field or a Cohen ring, so by ascent of N-2 along finite extensions it suffices that
these power series rings are N-2. This follows by induction on the number of variables from the
one-variable case; fields are N-2, and a Cohen ring is N-2 by Tate's criterion for the complete
principal ideal `(p)`.

## References

* [Stacks, Tag 032W]
-/

@[expose] public section

universe u

private instance mvPowerSeries_isDomain (σ : Type) (A : Type u)
    [CommRing A] [IsDomain A] : IsDomain (MvPowerSeries σ A) :=
  NoZeroDivisors.to_isDomain _

-- Allow any fraction field, including one in a different universe.
private theorem isN2_field (F : Type u) (K : Type*) [Field F] [Field K]
    [Algebra F K] [IsFractionRing F K] : IsN2 F K := by
  intro L _ _ _ _ _
  have : Module.Finite F K :=
    Module.Finite.equiv
      ((FractionRing.algEquiv F F).symm.trans (FractionRing.algEquiv F K)).toLinearEquiv
  have : Module.Finite F L := Module.Finite.trans K L
  exact Module.IsNoetherian.finite F (integralClosure F L)

-- An isomorphism is an injective finite extension, so N-2 ascends.
private theorem isN2_equiv (A B : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] (e : A ≃+* B)
    (hA : IsN2 A (FractionRing A)) : IsN2 B (FractionRing B) := by
  let : Algebra A B := e.toRingHom.toAlgebra
  have : Module.Finite A B := RingHom.Finite.of_surjective e.toRingHom e.surjective
  exact isN2_of_finite_domain_extension A B (FractionRing A) (FractionRing B)
    e.injective hA

-- Use the zero-variable and successor equivalences to iterate Tag 032Q.
private theorem isN2_mvPowerSeries (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hA : IsN2 A (FractionRing A)) (d : ℕ) :
    IsN2 (MvPowerSeries (Fin d) A) (FractionRing (MvPowerSeries (Fin d) A)) := by
  induction d with
  | zero =>
    exact isN2_equiv A _ (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv.symm hA
  | succ d ih =>
    have h := PowerSeries.noetherian_domain_isN2 (MvPowerSeries (Fin d) A) ih
    have : IsNoetherianRing (PowerSeries (MvPowerSeries (Fin d) A)) := h.1
    exact isN2_equiv _ _ (MvPowerSeries.finSuccEquiv A d).toRingEquiv.symm h.2.2

-- The quotient by p is a field, and Tate applies to the complete DVR.
private theorem isN2_cohen (A : Type u) [CommRing A] [IsDomain A] (p : ℕ)
    (hA : IsCohenRing p A) : IsN2 A (FractionRing A) := by
  obtain ⟨_, _, hdvr, hmax, hcomplete⟩ := hA
  have : IsDiscreteValuationRing A := hdvr
  have : IsAdicComplete (Ideal.span {(p : A)}) A := hcomplete
  have : (Ideal.span {(p : A)}).IsMaximal := by
    rw [← hmax]
    infer_instance
  let := Ideal.Quotient.field (Ideal.span {(p : A)})
  exact tate_n2_complete_principal A (FractionRing A) (p : A) inferInstance
    (isN2_field _ _)

-- Cohen structure supplies the finite power series subring.
private theorem isN2_complete_local_domain (D : Type u) [CommRing D]
    [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D] : IsN2 D (FractionRing D) := by
  obtain ⟨A, hreg, _, hfinite, _, _, _, hcoeff⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular D
  have : IsRegularLocalRing A := hreg
  have : Module.Finite A D := hfinite
  have hA : IsN2 A (FractionRing A) := by
    rcases hcoeff with ⟨k, hk, d, ⟨e⟩⟩ | ⟨Λ, hΛ, d, p, hp, ⟨e⟩⟩
    · let := hk
      exact isN2_equiv _ _ e.symm (isN2_mvPowerSeries k (isN2_field k _) d)
    · let := hΛ
      obtain ⟨hpprime, hdomain, hdvr, hmax, hcomp⟩ := hp
      have : IsDomain Λ := hdomain
      have : IsDiscreteValuationRing Λ := hdvr
      exact isN2_equiv _ _ e.symm
        (isN2_mvPowerSeries Λ (isN2_cohen Λ p ⟨hpprime, hdomain, hdvr, hmax, hcomp⟩) d)
  exact isN2_of_finite_domain_extension A D (FractionRing A) (FractionRing D)
    (fun x y h ↦ Subtype.ext h) hA

/-- A Noetherian ring complete at its unique maximal ideal is Nagata. -/
theorem isNagataRing_of_complete_local (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : IsNagataRing R := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  have hquot := quotient_complete_local R p hp.ne_top
  have : IsNoetherianRing (R ⧸ p) := hquot.1
  have : IsLocalRing (R ⧸ p) := hquot.2.1
  have : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ p)) (R ⧸ p) := hquot.2.2.2
  exact isN2_complete_local_domain (R ⧸ p)
