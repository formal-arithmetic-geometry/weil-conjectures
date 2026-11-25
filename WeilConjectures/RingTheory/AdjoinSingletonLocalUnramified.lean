/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdjoinSingletonPrincipalQuotientConditions
import WeilConjectures.RingTheory.AnalyticallyUnramifiedPrincipalCriterion
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing

/-!
# The local calculation for a fractional monogenic algebra

Let `R` be a Noetherian Nagata normal domain with fraction field `K` and `x ∈ K`. If `m` is a
maximal ideal of `R[x]` containing `x`, then `R[x]_m` is analytically unramified.

## References

* [Stacks Project, Tag 0334], Step 5
* [Stacks Project, Tag 0330], [Stacks Project, Tag 0331], [Stacks Project, Tag 031T]
-/

@[expose] public section

universe u v

/-- Let `R` be a Noetherian Nagata normal domain with fraction field `K`, and `x ∈ K` with `R[x]`
Noetherian. If `m` is a maximal ideal of `R[x]` containing `x`, then `R[x]_m` is analytically
unramified. -/
theorem isAnalyticallyUnramified_adjoin_singleton_atPrime_of_mem
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNagataRing R) (x : K)
    [IsNoetherianRing (Algebra.adjoin R ({x} : Set K))]
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hx : (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
      Algebra.adjoin R ({x} : Set K)) ∈ m) :
    IsAnalyticallyUnramified (Localization.AtPrime m) := by
  classical
  let S := Algebra.adjoin R ({x} : Set K)
  let A := Localization.AtPrime m
  by_cases hx0 : x = 0
  · have hxIntegral : IsIntegral R x := hx0 ▸ isIntegral_zero
    let : Module.Finite R S := Algebra.finite_adjoin_simple_of_isIntegral hxIntegral
    have hS : IsNagataRing S := (finite_over_nagata_is_nagata R S hR).1
    have hA : IsNagataRing A := (isNagataRing_localization S m.primeCompl hS).2.1 m
    exact isAnalyticallyUnramified_of_isNagataRing A hA
  · let tS : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
    let t : A := algebraMap S A tS
    have htS : tS ≠ 0 := by
      intro h
      exact hx0 (congrArg (fun z : S ↦ (z : K)) h)
    have ht : t ≠ 0 := by
      exact fun h ↦ htS ((IsLocalization.injective A m.primeCompl_le_nonZeroDivisors)
        (by simpa only [map_zero] using h))
    have htm : t ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m A]
      exact Ideal.mem_map_of_mem (algebraMap S A) hx
    obtain ⟨hnoEmbedded, hregular, hunramified⟩ :=
      adjoin_singleton_atPrime_principal_quotient_conditions R K hR x hx0 m hx
    exact isAnalyticallyUnramified_of_principal_quotient A t ht htm
      hnoEmbedded hregular hunramified
