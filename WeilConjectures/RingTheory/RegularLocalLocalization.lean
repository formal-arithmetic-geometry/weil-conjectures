/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.LocalizationFiniteGlobalDimension
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import WeilConjectures.RingTheory.RegularLocalOfFiniteGlobalDimension

/-! # Localization of a regular local ring

A prime localization of a regular local ring is regular local, so a regular local ring is a
regular ring.

## Implementation details

A regular local ring has finite global dimension, which is preserved by localization, and a
Noetherian local ring of finite global dimension is regular.

## References

* [Stacks, Tag 0AFS]
* [Stacks, Tag 00OD]
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- A prime localization of a regular local ring is regular local, and the ring is regular. -/
theorem localization_at_prime_and_isRegularRing
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) ∧ IsRegularRing R := by
  have hdim : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
    obtain ⟨a, ha⟩ := (WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R)))
    have ha_top : a ≠ ⊤ := by
      intro htop
      apply ringKrullDim_ne_top (R := R)
      simp [← ha, htop]
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp ha_top
    exact ⟨d, ha.symm.trans (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hd).symm⟩
  obtain ⟨d, hd⟩ := hdim
  have hgl : Ring.HasGlobalDimensionLE.{u, u} R d :=
    IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim_eq R d hd
  have hreg (q : Ideal R) [q.IsPrime] :
      IsRegularLocalRing (Localization.AtPrime q) := by
    have hglq : Ring.HasGlobalDimensionLE.{u, u} (Localization.AtPrime q) d := by
      exact (Ring.localization_preserves_projective_and_global_dimension R q.primeCompl d).2.1 hgl
    have hfdq : Ring.HasFiniteGlobalDimension.{u, u} (Localization.AtPrime q) := ⟨d, hglq⟩
    exact IsRegularLocalRing.of_hasFiniteGlobalDimension _ hfdq
  refine ⟨hreg p, ?_⟩
  apply isRegularRing_iff.mpr
  intro q hq
  exact hreg q

end IsRegularLocalRing
