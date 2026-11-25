/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres

/-!
# Normalization of a one-dimensional semilocal domain

We show that the normalization of a semilocal Noetherian domain of dimension one in its fraction
field is a semilocal Dedekind domain of dimension one with the same fraction field.

## Implementation details

Mathlib's `IsDedekindDomain` permits dimension zero, so dimension one is stated separately.
The statement is first proved for the canonical fraction field `FractionRing B`, which lies in
the universe of `B`, and then transported along the integral-closure equivalence induced by
`FractionRing B ≃ₐ[B] K`.

## References

* [Stacks, Tag 09N2]
* [Stacks, Tag 09IG]
-/

@[expose] public section

universe u v

namespace integralClosure

/-- Version of the normalization statement for a fraction field `K` in the universe of `B`: the
integral closure of `B` in `K` is semilocal and a Dedekind domain of dimension one. -/
private theorem normalization_same_universe
    (B K : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] [Field K] [Algebra B K] [IsFractionRing B K]
    (hdim : ringKrullDim B = 1) :
    Finite (MaximalSpectrum (integralClosure B K)) ∧
      IsDedekindDomain (integralClosure B K) ∧ ringKrullDim (integralClosure B K) = 1 := by
  classical
  obtain ⟨hD, hdimC, _, hfib, _⟩ :=
    AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres B K K hdim
  let C := integralClosure B K
  let f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B C))
  let g : MaximalSpectrum C → MaximalSpectrum B := fun x =>
    ⟨x.asIdeal.comap (algebraMap B C),
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal x.asIdeal⟩
  have hfinite (y : MaximalSpectrum B) : Finite (f ⁻¹' {y.toPrimeSpectrum}) :=
    hfib y.toPrimeSpectrum
  let j : MaximalSpectrum C → Σ y : MaximalSpectrum B, f ⁻¹' {y.toPrimeSpectrum} :=
    fun x => ⟨g x, ⟨x.toPrimeSpectrum, by rfl⟩⟩
  have hj : Function.Injective j := by
    intro x z hxz
    have hp : x.toPrimeSpectrum = z.toPrimeSpectrum := by
      exact congrArg (fun t => t.2.1) hxz
    exact MaximalSpectrum.toPrimeSpectrum_injective hp
  exact ⟨Finite.of_injective j hj, hD, hdimC⟩

/-- The normalization of a semilocal Noetherian domain of dimension one in its fraction
field is semilocal, Noetherian, an integrally closed domain of dimension one, and has
that same fraction field. -/
theorem semilocal_normalization_dim_one
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K] :
    Finite (MaximalSpectrum (integralClosure B K)) ∧
      IsDedekindDomain (integralClosure B K) ∧ ringKrullDim (integralClosure B K) = 1 ∧
      IsFractionRing (integralClosure B K) K := by
  let F := FractionRing B
  obtain ⟨hfinite, hD, hdimF⟩ := normalization_same_universe B F hdim
  have : Finite (MaximalSpectrum (integralClosure B F)) := hfinite
  have : IsDedekindDomain (integralClosure B F) := hD
  let e := (FractionRing.algEquiv B K).mapIntegralClosure
  have : IsNoetherianRing (integralClosure B K) :=
    isNoetherianRing_of_ringEquiv (integralClosure B F) e.toRingEquiv
  have : Ring.DimensionLEOne (integralClosure B K) :=
    Ring.DimensionLEOne.of_ringEquiv e.symm.toRingEquiv
  have : IsIntegrallyClosed (integralClosure B K) :=
    IsIntegrallyClosed.of_equiv e.toRingEquiv
  have hD' : IsDedekindDomain (integralClosure B K) := { }
  let j : MaximalSpectrum (integralClosure B K) →
      MaximalSpectrum (integralClosure B F) := fun x =>
    ⟨x.asIdeal.comap e.toRingHom,
      x.isMaximal.comap_bijective e.toRingHom e.bijective⟩
  have hj : Function.Injective j := by
    intro x z h
    apply MaximalSpectrum.ext
    have h' := congrArg MaximalSpectrum.asIdeal h
    exact (Ideal.relIsoOfBijective e.toRingHom e.bijective).injective h'
  exact ⟨Finite.of_injective j hj, hD',
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans hdimF,
    isFractionRing_of_finite_extension K K⟩

end integralClosure
