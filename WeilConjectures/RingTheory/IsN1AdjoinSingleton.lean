/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AsSubring
import WeilConjectures.RingTheory.IsN1OfFiniteDomainExtension
import WeilConjectures.RingTheory.IsN1OfIsAnalyticallyUnramified
import WeilConjectures.RingTheory.IsN1OfLocalCharacterization
import WeilConjectures.RingTheory.AdjoinSingletonLocalUnramified
import WeilConjectures.RingTheory.AdjoinSingletonMaximalFiniteCover

/-!
# Normalization of a monogenic subalgebra of a normal Nagata domain's fraction field

For a normal Nagata domain `R` with fraction field `K` and `x ∈ K`, the subring `R[x]` of `K`
is N-1.

## Implementation details

By the local characterization of N-1 it suffices to treat the localizations of `S = R[x]` at
maximal ideals `m`. After adjoining the roots of a lift of the minimal polynomial of the residue
of `x` and passing to the (finite) integral closure, one may assume `x ∈ m`. Then
`S/xS ≅ R/(R ∩ xR)` has no embedded associated primes, all of height one, the localizations of
`S` at them are discrete valuation rings, and the quotients are Nagata local domains; the
principal criterion shows that `S_m` is analytically unramified, hence N-1. The result descends
along the finite extension by the finite-extension descent of N-1.

## References

* [Stacks, Tag 0334]
-/

@[expose] public section

universe u v

/-- Clearing one denominator identifies a principal open of `R[x]` with one of `R`. -/
private theorem adjoin_singleton_normal_away (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) :
    ∃ f : Algebra.adjoin R ({x} : Set K), f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  obtain ⟨b, a, hx⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.property
  let S := Algebra.adjoin R ({x} : Set K)
  let M := Submonoid.powers (a : R)
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  let T := Localization.subalgebra K M hM
  have hxT : x ∈ T := by
    refine ⟨b, a, Submonoid.mem_powers _, ?_⟩
    exact hx.symm
  have hST : S ≤ T := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxT)
  let : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let f : S := algebraMap R S a
  have hf : f ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective R K
    have := congrArg (fun z : S ↦ (z : K)) h
    simpa only [f, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero, map_zero] using this
  let : IsLocalization.Away f T := by
    refine IsLocalization.Away.mk f ?_ ?_ ?_
    · change IsUnit (algebraMap R T a)
      exact IsLocalization.Away.algebraMap_isUnit (a : R)
    · intro t
      obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (a : R) t
      exact ⟨n, algebraMap R S r, hr⟩
    · intro c d h
      have hcd : c = d := Subtype.ext (congrArg (fun z : T ↦ (z : K)) h)
      exact ⟨0, by simp [hcd]⟩
  let : IsIntegrallyClosed T := isIntegrallyClosed_of_isLocalization T M hM
  let e : T ≃ₐ[S] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) T (Localization.Away f)
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  refine ⟨f, hf, ?_⟩
  intro p hp
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization
    (Localization.AtPrime p) p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

/-- For a normal Nagata domain `R` with fraction field `K`, the subring `R[x]` of `K`
is N-1: its integral closure in `K` is finite as an `R[x]`-module. -/
theorem isN1_adjoin_singleton_of_isNagataRing (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : IsNagataRing R) (x : K) :
    IsN1 (Algebra.adjoin R ({x} : Set K)) K := by
  let : IsNoetherianRing R := hR.1
  let S := Algebra.adjoin R ({x} : Set K)
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isN1_of_local_characterization S K (adjoin_singleton_normal_away R K x)
  intro m hm
  obtain ⟨B, hComm, hDomain, hAlg, hNoeth, hInjective, hFinite, hAway, hMax⟩ :=
    exists_finite_cover_adjoin_singleton_atPrime R K hR x m
      (fun R' K' _ _ _ _ _ _ _ hR' y _ q _ hy ↦
        isAnalyticallyUnramified_adjoin_singleton_atPrime_of_mem R' K' hR' y q hy)
  let := hComm
  let := hDomain
  let := hAlg
  let := hNoeth
  let := hFinite
  have hB : IsN1 B (FractionRing B) :=
    isN1_of_local_characterization B (FractionRing B) hAway
      (fun q _ ↦ isN1_of_isAnalyticallyUnramified
        (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) (hMax q))
  exact isN1_of_finite_domain_extension (Localization.AtPrime m) B
    (FractionRing (Localization.AtPrime m)) (FractionRing B) hInjective hB
