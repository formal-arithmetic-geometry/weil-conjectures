/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.AnnihilatorAssociatedPrimes
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Localization at an associated prime

Source: Stacks Project, Algebra, Lemma 0310 (1), `lemma-associated-primes-localize`
(blueprint: lem-weil-pbc-associated-prime-localize-at-prime).
-/

@[expose] public section

universe u v

namespace Module

/-- Localization preserves an annihilator-defined associated prime.
Source: Stacks Project, Algebra, Lemma 0310 (1), lines 15393-15410.
(blueprint: lem-weil-pbc-associated-prime-localize-at-prime)

If `Ann_T(z) = q`, the contraction of the annihilator of `z/1` consists of the
scalars `a` for which some `t ∉ q` kills `a • z`. Equivalently, `t * a ∈ q` for
some `t ∉ q`, which by primality is equivalent to `a ∈ q`. The localization ideal
correspondence (`IsLocalization.map_under`) then identifies the annihilator with
`q T_q`. Finally, this extended ideal is prime, and any witness for the original
association supplies a witness for the localized association. This computes the
annihilator directly using the zero-fraction criterion, without exactness. -/
theorem associated_prime_localize_at_prime
    {T : Type u} [CommRing T] {P : Type v} [AddCommGroup P] [Module T P]
    {q : Ideal T} [hq : q.IsPrime]
    (hqmem : q ∈ RingTheory.annihilatorAssociatedPrimes T P) :
    q.map (algebraMap T (Localization.AtPrime q)) ∈
      RingTheory.annihilatorAssociatedPrimes (Localization.AtPrime q)
        (LocalizedModule.AtPrime q P) ∧
    ∀ z : P, (⊥ : Submodule T P).colon {z} = q →
      (⊥ : Submodule (Localization.AtPrime q) (LocalizedModule.AtPrime q P)).colon
          {LocalizedModule.mk z 1} = q.map (algebraMap T (Localization.AtPrime q)) := by
  have hann : ∀ z : P, (⊥ : Submodule T P).colon {z} = q →
      (⊥ : Submodule (Localization.AtPrime q) (LocalizedModule.AtPrime q P)).colon
          {LocalizedModule.mk z 1} = q.map (algebraMap T (Localization.AtPrime q)) := by
    intro z hz
    let J := (⊥ : Submodule (Localization.AtPrime q)
      (LocalizedModule.AtPrime q P)).colon {LocalizedModule.mk z 1}
    have hcontract : J.under T = q := by
      ext a
      change algebraMap T (Localization.AtPrime q) a ∈ J ↔ a ∈ q
      simp only [J, Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul]
      rw [← LocalizedModule.mkLinearMap_apply, ← LinearMap.map_smul]
      rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
      constructor
      · rintro ⟨t, ht, htz⟩
        have hta : t * a ∈ q := by
          rw [← hz, Submodule.mem_colon_singleton, Submodule.mem_bot, mul_smul]
          exact htz
        exact (hq.mem_or_mem hta).resolve_left ht
      · intro ha
        refine ⟨1, q.primeCompl.one_mem, ?_⟩
        have haz : a • z = 0 := by
          simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using
            (show a ∈ (⊥ : Submodule T P).colon {z} from hz.symm ▸ ha)
        simp [haz]
    exact (IsLocalization.map_under q.primeCompl (Localization.AtPrime q) J).symm.trans
      (congrArg (Ideal.map (algebraMap T (Localization.AtPrime q))) hcontract)
  refine ⟨?_, hann⟩
  rcases hqmem with ⟨_, z, hz⟩
  exact ⟨Ideal.isPrime_map_of_isLocalizationAtPrime q le_rfl,
    LocalizedModule.mk z 1, (hann z hz.symm).symm⟩

end Module
