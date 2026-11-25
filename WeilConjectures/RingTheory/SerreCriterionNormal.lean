/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.NormalLocalDepthTwo
import WeilConjectures.RingTheory.IntegralTotalFractionLocalDenominator
import WeilConjectures.RingTheory.SerreS2TotalFractionMembership
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Serre's criterion for normality

We prove Serre's criterion: a Noetherian ring is normal if and only if it satisfies the
conditions `(R₁)` and `(S₂)`.

## References

* [Stacks, Tag 031S]
-/

@[expose] public section

universe u

namespace Ring

/-- A Noetherian ring is normal (all localizations at primes are integrally closed domains)
if and only if it satisfies `(R₁)` and `(S₂)`. -/
theorem forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS (R : Type u) [CommRing R]
    [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    IsSerreR R 1 ∧ IsSerreS R 2 := by
  constructor
  · intro hnormal
    refine ⟨?_, ?_⟩
    · intro p hp hheight
      have h := hnormal p
      let := h.1
      let := h.2
      apply IsRegularLocalRing.of_isIntegrallyClosed
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact_mod_cast hheight
    · intro p hp
      have h := hnormal p
      let := h.1
      let := h.2
      by_cases hheight : p.height ≤ 1
      · by_cases hz : p.height = 0
        · simp [hz]
        · have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
            have : p.height = 1 := by
              exact le_antisymm hheight (Order.one_le_iff_ne_zero.mpr hz)
            exact_mod_cast this
          have hdepth : (1 : ℕ∞) ≤
              IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) := by
            let A := Localization.AtPrime p
            have hm : IsLocalRing.maximalIdeal A ≠ ⊥ := by
              intro hm
              have hf := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
              let := hf.toField
              have hz := ringKrullDim_eq_zero_of_field A
              rw [hdim] at hz
              norm_num at hz
            obtain ⟨x, hxm, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
            have hxreg : RingTheory.Sequence.IsRegular A [x] := by
              refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff A x).mpr
                (fun a b hab ↦ mul_left_cancel₀ hx hab), ?_⟩
              rw [Ideal.ofList_singleton, Ideal.smul_eq_mul, Ideal.mul_top]
              intro heq
              have hspan : Ideal.span {x} ≤ IsLocalRing.maximalIdeal A :=
                Ideal.span_le.mpr (by simpa using hxm)
              exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
                (top_unique (heq ▸ hspan))
            unfold IsLocalRing.depth Ideal.depth
            split_ifs
            · exact le_top
            · apply le_sSup
              exact ⟨[x], hxreg, by simpa using hxm, by simp⟩
          exact (min_le_right _ _).trans (hheight.trans hdepth)
      · have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p) := by
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
          have htwo : (2 : ℕ∞) ≤ p.height := by
            have h := (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
              (lt_of_not_ge hheight)
            norm_num at h ⊢
            exact h
          exact WithBot.coe_le_coe.mpr htwo
        exact (min_le_left _ _).trans
          (IsLocalRing.depth_two_of_normal (Localization.AtPrime p) hdim)
  · rintro ⟨hR, hS⟩
    have hRzero : IsSerreR R 0 := by
      intro p hp hheight
      exact hR p (hheight.trans (by simp))
    have hSone : IsSerreS R 1 := by
      intro p hp
      exact (min_le_min_right p.height (by simp : (1 : ℕ∞) ≤ 2)).trans (hS p)
    let := (isReduced_iff_serreR_zero_and_serreS_one R).mpr ⟨hRzero, hSone⟩
    apply (reduced_normal_iff_integrallyClosed_totalFractions R
      (minimalPrimes.finite_of_isNoetherianRing R)).1.mpr
    refine isIntegrallyClosedIn_iff.mpr ⟨IsFractionRing.injective R (FractionRing R), ?_⟩
    intro x hx
    apply exists_algebraMap_eq_of_serreS_two R hS x
    intro p hp hheight
    let := hR p hheight
    let := IsRegularLocalRing.isDomain (Localization.AtPrime p)
    have hdim : ringKrullDim (Localization.AtPrime p) ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact_mod_cast hheight
    let := IsRegularLocalRing.isIntegrallyClosed (Localization.AtPrime p) hdim
    exact hx.exists_local_denominator_of_normal p

end Ring
