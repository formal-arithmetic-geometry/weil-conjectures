/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Prime ideals, local rings and residue fields of a localization

A localization `A → A'` at `W` induces a bijection between primes of `A'` and primes of `A`
disjoint from `W`, together with canonical isomorphisms of the local rings and residue fields.

## Implementation details

The extension of a prime `p` disjoint from `W` consists of fractions with numerator in `p`, and
the localization kernel condition shows its contraction is `p`. The local ring isomorphism comes
from uniqueness of localization, since `A'_{q'}` is a localization of `A` at the complement of
`q`; its ring map is `Localization.localRingHom`. The residue field isomorphism is induced on the
quotients by the maximal ideals.

## References

* [Stacks, Tags 00E3, 00C9, 07BH]
-/

@[expose] public section

universe u v

namespace IsLocalization

/-- A localization induces the prime-ideal correspondence and canonical isomorphisms of
local rings and residue fields. -/
theorem prime_localRing_residueField_iso
    (A : Type u) (A' : Type v) [CommRing A] [CommRing A'] [Algebra A A']
    (W : Submonoid A) [IsLocalization W A'] (q' : Ideal A') [q'.IsPrime] :
    let q := q'.comap (algebraMap A A')
    q.IsPrime ∧ Disjoint (W : Set A) (q : Set A) ∧
      (∀ p : Ideal A, p.IsPrime → Disjoint (W : Set A) (p : Set A) →
        (p.map (algebraMap A A')).IsPrime ∧
          (p.map (algebraMap A A')).comap (algebraMap A A') = p) ∧
      q.map (algebraMap A A') = q' ∧
      Set.BijOn (Ideal.comap (algebraMap A A')) {r : Ideal A' | r.IsPrime}
        {p : Ideal A | p.IsPrime ∧ Disjoint (W : Set A) (p : Set A)} ∧
      IsLocalization.AtPrime (Localization.AtPrime q') q ∧
      ∃ e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime q',
        e.toRingHom = Localization.localRingHom q q' (algebraMap A A') rfl ∧
        (q.map (algebraMap A (Localization.AtPrime q))).map e.toRingHom =
          q'.map (algebraMap A' (Localization.AtPrime q')) ∧
        ∃ σ : q.ResidueField ≃ₐ[A] q'.ResidueField,
          ∀ x : Localization.AtPrime q,
            σ (IsLocalRing.residue (Localization.AtPrime q) x) =
              IsLocalRing.residue (Localization.AtPrime q') (e x) := by
  let q := q'.comap (algebraMap A A')
  have hq := (isPrime_iff_isPrime_disjoint W A' q').mp inferInstance
  let : q.IsPrime := hq.1
  have hp : ∀ p : Ideal A, p.IsPrime → Disjoint (W : Set A) (p : Set A) →
      (p.map (algebraMap A A')).IsPrime ∧
        (p.map (algebraMap A A')).comap (algebraMap A A') = p := by
    intro p hprime hd
    exact ⟨isPrime_of_isPrime_disjoint W A' p hprime hd,
      under_map_of_isPrime_disjoint W A' hprime hd⟩
  have hbij : Set.BijOn (Ideal.comap (algebraMap A A')) {r : Ideal A' | r.IsPrime}
      {p : Ideal A | p.IsPrime ∧ Disjoint (W : Set A) (p : Set A)} := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      exact (isPrime_iff_isPrime_disjoint W A' r).mp hr
    · intro r hr s hs hrs
      exact (orderEmbedding W A').injective hrs
    · intro p hp'
      exact ⟨p.map (algebraMap A A'), (hp p hp'.1 hp'.2).1,
        (hp p hp'.1 hp'.2).2⟩
  let : IsLocalization.AtPrime (Localization.AtPrime q') q :=
    isLocalization_isLocalization_atPrime_isLocalization W (Localization.AtPrime q') q'
  refine ⟨hq.1, hq.2, hp, map_under W A' q', hbij, inferInstance, ?_⟩
  let e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime q' :=
    IsLocalization.algEquiv q.primeCompl _ _
  refine ⟨e, ?_, ?_, IsLocalRing.ResidueField.mapAlgEquiv e, ?_⟩
  · exact (Localization.localRingHom_unique q q' (algebraMap A A') rfl
      (fun x ↦ by
        change e (algebraMap A (Localization.AtPrime q) x) = _
        rw [← IsScalarTower.algebraMap_apply A A' (Localization.AtPrime q')]
        exact e.commutes x)).symm
  · rw [Localization.AtPrime.map_eq_maximalIdeal,
      Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  · intro x
    exact IsLocalRing.ResidueField.mapAlgEquiv_residue e x

end IsLocalization
