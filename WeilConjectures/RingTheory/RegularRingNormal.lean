/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.SerreConditions
import WeilConjectures.RingTheory.SerreCriterionNormal

/-!
# A regular ring is normal

A regular ring is normal.

## Implementation details

Regular local rings satisfy `(R_1)`, and a regular system of parameters is a regular sequence
(Tag 00NQ), giving `(S_2)`. Serre's criterion (Tag 031S) then gives normality.

## References

* [Stacks, Tag 0567]
* [Stacks, Tags 00NQ, 031S]
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Every localization of a regular ring at a prime ideal is a normal domain. -/
theorem isNormalRing (R : Type u) [CommRing R] [IsRegularRing R] :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  apply (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS R).mpr
  constructor
  · intro p hp
    exact inferInstance
  · classical
    intro p hp
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    obtain ⟨s, hcard, hs⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
    let rs := s.toList
    have hspan : Ideal.span {x | x ∈ rs} = m := by
      simpa [rs] using hs
    have hdim : ringKrullDim A = (rs.length : WithBot ℕ∞) := by
      simpa [rs, hcard, m] using
        (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
    have hparams : IsLocalRing.IsRegularSystemOfParameters rs := ⟨hspan, hdim.symm⟩
    have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
      A rs.length hdim rs hparams).1
    have hmem : ∀ x ∈ rs, x ∈ m := by
      intro x hx
      rw [← hspan]
      exact Ideal.subset_span hx
    have hdepth : (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
      unfold IsLocalRing.depth Ideal.depth
      split_ifs
      · exact le_top
      · exact le_sSup ⟨rs, hreg, hmem, rfl⟩
    have hheight : p.height = (rs.length : ℕ∞) := by
      have h := (IsLocalization.AtPrime.ringKrullDim_eq_height p A).symm.trans hdim
      exact WithBot.coe_inj.mp h
    exact (min_le_right _ _).trans (hheight ▸ hdepth)

end IsRegularRing
