/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Primes and residue fields of a localization

Let `A → A'` be a localization at a multiplicative subset `W`. Primes of `A'` correspond to the
primes of `A` disjoint from `W`, and corresponding primes have isomorphic local rings and residue
fields.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalization

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (W : Submonoid A)
  [IsLocalization W A']

/-- **Primes, local rings and residue fields of a localization.** Let `A' = W⁻¹A` and let `q'` be
a prime of `A'` with contraction `q` to `A`. Then
1. `q` is prime and disjoint from `W`; for every prime `p` of `A` disjoint from `W`, `pA'` is
   prime with contraction `p`; and `qA' = q'` (so primes of `A'` correspond to primes of `A`
   disjoint from `W`);
2. `A'_{q'}` is a localization of `A` at `A \ q`, so `A_q ≃ₐ[A] A'_{q'}`;
3. this isomorphism carries `qA_q` onto `q'A'_{q'}` and induces an `A`-algebra isomorphism of
   residue fields `κ(q) ≃ κ(q')`.

(blueprint: `lem-weil-pbc-localization-prime-residue-field-iso`) -/
theorem prime_localRing_residueField_iso (q' : Ideal A') [q'.IsPrime] :
    ((q'.under A).IsPrime ∧ Disjoint (W : Set A) (q'.under A)) ∧
    (∀ p : Ideal A, p.IsPrime → Disjoint (W : Set A) p →
      (p.map (algebraMap A A')).IsPrime ∧ (p.map (algebraMap A A')).under A = p) ∧
    (q'.under A).map (algebraMap A A') = q' ∧
    IsLocalization (q'.under A).primeCompl (Localization.AtPrime q') ∧
    ∃ e : Localization.AtPrime (q'.under A) ≃ₐ[A] Localization.AtPrime q',
      (∀ x, x ∈ maximalIdeal _ ↔ e x ∈ maximalIdeal (Localization.AtPrime q')) ∧
      ∃ σ : (q'.under A).ResidueField ≃ₐ[A] q'.ResidueField,
        ∀ x, σ (residue _ x) = residue _ (e x) := by
  have hloc : IsLocalization (q'.under A).primeCompl (Localization.AtPrime q') :=
    isLocalization_isLocalization_atPrime_isLocalization W _ q'
  refine ⟨⟨inferInstance, (disjoint_under_iff W A' q').2 (Ideal.IsPrime.ne_top ‹_›)⟩,
    fun p hp hd => ⟨isPrime_of_isPrime_disjoint W A' p hp hd,
      under_map_of_isPrime_disjoint W A' hp hd⟩, map_under W A' q', hloc, ?_⟩
  let e : Localization.AtPrime (q'.under A) ≃ₐ[A] Localization.AtPrime q' :=
    IsLocalization.algEquiv (q'.under A).primeCompl _ _
  exact ⟨e, fun x => by simp [mem_maximalIdeal, mem_nonunits_iff],
    ResidueField.mapAlgEquiv e, fun _ => rfl⟩

end IsLocalization
