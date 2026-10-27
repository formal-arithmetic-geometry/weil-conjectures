/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Weak association detected by localization at a prime

Source: Stacks Project, Algebra, Lemma 10.66.2, Tag 0566
(blueprint: lem-sc-weakass-localization).
-/

@[expose] public section

universe u v

namespace Module

/-- Clearing denominators identifies the annihilator of `m/s` with the extended annihilator
of `m`, independently of the denominator. -/
private theorem colon_localized_mk
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (m : M) (s : p.primeCompl) :
    ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
      {IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl M) m s}) =
        ((⊥ : Submodule R M).colon {m}).map
          (algebraMap R (Localization.AtPrime p)) := by
  ext z
  obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
    IsLocalizedModule.mk'_smul_mk', IsLocalizedModule.mk'_eq_zero',
    IsLocalization.mk'_mem_map_algebraMap_iff p.primeCompl]
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, mul_smul]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, a.2, ha⟩, fun ⟨a, ha, h⟩ ↦ ⟨⟨a, ha⟩, h⟩⟩

/-- Weak association of `p` to `M`, weak association of its extension to `Mₚ`, and existence
of an element of `Mₚ` whose annihilator has radical `p Rₚ` are equivalent.
Source: Stacks Project, Algebra, Lemma 10.66.2, Tag 0566
(blueprint: lem-sc-weakass-localization).

Proof:
1. Suppose `p` is minimal over `Ann_R(m) = I`. The annihilator of `m/1` is `I Rₚ`:
   if `(r/s)(m/1) = 0`, some `t ∉ p` satisfies `trm = 0`, and `r/s = (tr)/(ts)`
   belongs to the extended ideal; the other inclusion follows from scalar multiplication.
   The prime correspondence of `lem-weil-pbc-primes-of-localization` identifies primes
   of `Rₚ` with primes of `R` contained in `p`. Thus the only prime containing `I Rₚ`
   is `p Rₚ`, and the intersection-of-primes description of the radical gives clause (3).
2. If an element's annihilator has radical `p Rₚ`, every prime containing that
   annihilator contains its radical. Since `p Rₚ` is prime, it is minimal over the
   annihilator, giving clause (2).
3. Conversely, write a witness for clause (2) as `m/s`. Multiplication by the unit `s`
   preserves its annihilator, so `p Rₚ` is minimal over `Ann_R(m) Rₚ`, by the same
   denominator calculation as in step 1. The prime correspondence of
   `lem-weil-pbc-primes-of-localization` contracts `p Rₚ` to `p`, which therefore
   contains `Ann_R(m)`. A strictly smaller prime containing `Ann_R(m)` would extend
   to a strictly smaller prime containing the localized annihilator, contradicting
   minimality. This gives clause (1). -/
theorem weakly_associated_atPrime_iff
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] :
    ((∃ m : M, p ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes) ↔
      (∃ x : LocalizedModule.AtPrime p M,
        p.map (algebraMap R (Localization.AtPrime p)) ∈
          ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
            {x}).minimalPrimes)) ∧
    ((∃ x : LocalizedModule.AtPrime p M,
        p.map (algebraMap R (Localization.AtPrime p)) ∈
          ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
            {x}).minimalPrimes) ↔
      (∃ x : LocalizedModule.AtPrime p M,
        ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
          {x}).radical = p.map (algebraMap R (Localization.AtPrime p)))) := by
  let A := Localization.AtPrime p
  let f := LocalizedModule.mkLinearMap p.primeCompl M
  have under : (p.map (algebraMap R A)).under R = p := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p A,
      IsLocalization.AtPrime.under_maximalIdeal A p]
  have min_iff (m : M) (s : p.primeCompl) :
      p.map (algebraMap R A) ∈
        ((⊥ : Submodule A (LocalizedModule.AtPrime p M)).colon
          {IsLocalizedModule.mk' f m s}).minimalPrimes ↔
        p ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes := by
    rw [colon_localized_mk, IsLocalization.minimalPrimes_map p.primeCompl A,
      Set.mem_preimage, under]
  constructor
  · constructor
    · rintro ⟨m, hm⟩
      exact ⟨IsLocalizedModule.mk' f m 1, (min_iff m 1).mpr hm⟩
    · rintro ⟨x, hx⟩
      obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl f x
      exact ⟨m, (min_iff m s).mp hx⟩
  · constructor
    · rintro ⟨x, hx⟩
      obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl f x
      refine ⟨IsLocalizedModule.mk' f m s, ?_⟩
      rw [colon_localized_mk]
      exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p _
        ((min_iff m s).mp hx)
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← Ideal.radical_minimalPrimes, hx, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _

end Module
