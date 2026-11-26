/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.DVRCompletionRegular
import WeilConjectures.RingTheory.IntegerPrimeLocalizations
import WeilConjectures.RingTheory.LocalizationRegular
import Mathlib.Algebra.CharP.Algebra

/-!
# The integers are a G-ring

## Implementation details

By the maximal-ideal criterion it suffices to check that the completion maps of the
localizations of `ℤ` at primes are regular: at the zero prime the localization is the field `ℚ`,
and at a nonzero prime it is a discrete valuation ring with fraction field of characteristic
zero, whose completion map is regular.

## References

* [Stacks, Tag 07PX]
-/

@[expose] public section

namespace Int

/-- The ring of integers is a G-ring. -/
theorem isGRing : IsGRing ℤ := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    obtain ⟨e⟩ := prime_localizations_dvr.2.2.2.2.1
    let A := Localization.AtPrime (⊥ : Ideal ℤ)
    let : Field A := (e.toRingEquiv.toMulEquiv.isField (Field.toIsField ℚ)).toField
    have hm : IsLocalRing.maximalIdeal A = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
      rw [hm]
      infer_instance
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    have hb : Function.Bijective (algebraMap A C) := by
      exact (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal A)).bijective
    have : IsLocalization (⊥ : Submonoid A) C :=
      IsLocalization.of_le_isUnit_of_bijective (by
        rintro x ⟨y, hy, rfl⟩
        have : y = 1 := hy
        simp [this]) hb
    exact (IsLocalization.isRegular_and_fiber (⊥ : Submonoid A)).1
  · let A := Localization.AtPrime p
    have : IsDiscreteValuationRing A := (prime_localizations_dvr.2.2.2.2.2 p h).2.2.1
    have : CharZero A := charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℤ A)
    have : CharZero (FractionRing A) := IsFractionRing.charZero_of_isFractionRing A
    exact AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero
      A (FractionRing A)

end Int
