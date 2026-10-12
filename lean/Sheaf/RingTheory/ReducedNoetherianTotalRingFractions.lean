/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Algebra.Pi

/-!
# Total ring of fractions of a reduced Noetherian ring

Source: literature/stacks-project/algebra.tex, Lemma Tag 02LX (blueprint:
lem-weil-pbc-reduced-noetherian-total-ring-fractions).
-/

@[expose] public section

universe u

private theorem minimalPrime_of_disjoint
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (p : Ideal R) [p.IsPrime]
    (hd : Disjoint (nonZeroDivisors R : Set R) (p : Set R)) :
    p ∈ minimalPrimes R := by
  classical
  let s := (minimalPrimes.finite_of_isNoetherianRing R).toFinset
  have hsub : (p : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), (i : Set R) := by
    intro x hx
    have hn : x ∉ nonZeroDivisors R := fun hs ↦ Set.disjoint_left.mp hd hs hx
    obtain ⟨y, hxy, hy⟩ := notMem_nonZeroDivisors_iff_left.mp hn
    have hu : x ∈ ⋃ i ∈ (minimalPrimes R), (i : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      exact ⟨y, by simpa using hy, by simpa using hxy⟩
    simpa [s] using hu
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
    (fun i hi _ _ ↦ ((minimalPrimes.finite_of_isNoetherianRing R).mem_toFinset.mp hi).isPrime)
      ).mp hsub
  have hqm : q ∈ minimalPrimes R :=
    (minimalPrimes.finite_of_isNoetherianRing R).mem_toFinset.mp hq
  have heq : p = q := hpq.antisymm (hqm.2 ⟨inferInstance, bot_le⟩ hpq)
  exact heq ▸ hqm

/-- The component map is injective; this is the injectivity half of the finite
product decomposition of the total ring of fractions.
(blueprint: lem-weil-pbc-fraction-ring-pi-injective)
-/
theorem fractionRing_pi_injective_of_compatible
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    {t : ℕ} {q : Fin t ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}}
    (φ : ∀ i : Fin t, FractionRing R →+* Localization.AtPrime (q i).val.asIdeal)
    (hφ : ∀ i : Fin t, (φ i).comp (algebraMap R (FractionRing R)) =
      algebraMap R (Localization.AtPrime (q i).val.asIdeal)) :
    Function.Injective (RingHom.pi φ) := by
  sorry

/-- The component map is surjective; this is the surjectivity half of the finite
product decomposition of the total ring of fractions.
(blueprint: lem-weil-pbc-fraction-ring-pi-surjective)
-/
theorem fractionRing_pi_surjective_of_compatible
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    {t : ℕ} {q : Fin t ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}}
    (φ : ∀ i : Fin t, FractionRing R →+* Localization.AtPrime (q i).val.asIdeal)
    (hφ : ∀ i : Fin t, (φ i).comp (algebraMap R (FractionRing R)) =
      algebraMap R (Localization.AtPrime (q i).val.asIdeal)) :
    Function.Surjective (RingHom.pi φ) := by
  sorry

/-- The total ring of fractions of a reduced Noetherian ring is the product of
localizations at its minimal primes
(blueprint: lem-weil-pbc-reduced-noetherian-total-ring-fractions).
Proof steps (Stacks Tags 00EW, 00EU, 00FR, 02LX): (1) finiteness of the minimal
primes gives the finite indexing equivalence; at each minimal prime, reducedness
and minimality make the localization a field with zero extended prime, so it is
the residue field. (2) The zero-divisors are the union of the minimal primes, so
the nonzerodivisors avoid each one; the universal property of localization gives
the unique compatible maps from the total fraction ring. (3) Localization's prime
correspondence and prime avoidance show that the primes of the total fraction
ring are precisely the extended minimal primes, which are all maximal. (4) The
product decomposition for a ring with finitely many maximal ideals identifies the
total fraction ring with the product of its localizations there. (5) The
localization correspondence identifies each factor with the corresponding
localization of the original ring, and uniqueness identifies the resulting map
with the componentwise map in the statement. -/
theorem fractionRing_pi_bijective_of_compatible
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    {t : ℕ} {q : Fin t ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}}
    (φ : ∀ i : Fin t, FractionRing R →+* Localization.AtPrime (q i).val.asIdeal)
    (hφ : ∀ i : Fin t, (φ i).comp (algebraMap R (FractionRing R)) =
      algebraMap R (Localization.AtPrime (q i).val.asIdeal)) :
    Function.Bijective (RingHom.pi φ) := by
  exact ⟨fractionRing_pi_injective_of_compatible φ hφ,
    fractionRing_pi_surjective_of_compatible φ hφ⟩

theorem reduced_noetherian_total_ring_fractions
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R] :
    ∃ t : ℕ,
      ∃ q : Fin t ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R},
        (∀ i : Fin t, IsField (Localization.AtPrime (q i).val.asIdeal)) ∧
          (∀ i : Fin t,
            Ideal.map (algebraMap R (Localization.AtPrime (q i).val.asIdeal))
                (q i).val.asIdeal = ⊥) ∧
          (∀ i : Fin t,
            Function.Bijective
              (algebraMap (Localization.AtPrime (q i).val.asIdeal)
                (Ideal.ResidueField (q i).val.asIdeal))) ∧
          (∀ i : Fin t, ∀ s : R,
            s ∈ nonZeroDivisors R → s ∉ (q i).val.asIdeal) ∧
          (∀ i : Fin t,
            ∃! φ : FractionRing R →+* Localization.AtPrime (q i).val.asIdeal,
              φ.comp (algebraMap R (FractionRing R)) =
                algebraMap R (Localization.AtPrime (q i).val.asIdeal)) ∧
          (∀ φ : ∀ i : Fin t, FractionRing R →+* Localization.AtPrime (q i).val.asIdeal,
            (∀ i : Fin t, (φ i).comp (algebraMap R (FractionRing R)) =
                algebraMap R (Localization.AtPrime (q i).val.asIdeal)) →
              Function.Bijective (RingHom.pi φ)) := by
  classical
  let M := {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}
  let : Finite {p : Ideal R // p ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).fintype.finite
  have : Finite M := Finite.of_injective
    (fun p : M ↦ (⟨p.1.asIdeal, p.2⟩ : minimalPrimes R))
    (fun p q h ↦ Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h)))
  let : Fintype M := Fintype.ofFinite M
  let q : Fin (Fintype.card M) ≃ M := (Fintype.equivFin M).symm
  have hfield (i : Fin (Fintype.card M)) :
      IsField (Localization.AtPrime (q i).1.asIdeal) := by
    have := Ring.KrullDimLE.of_isLocalization (q i).1.asIdeal (q i).2
      (Localization.AtPrime (q i).1.asIdeal)
    exact Ring.KrullDimLE.isField_of_isReduced
  have hzero (i : Fin (Fintype.card M)) :
      Ideal.map (algebraMap R (Localization.AtPrime (q i).1.asIdeal))
        (q i).1.asIdeal = ⊥ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.mp (hfield i)
  have hres (i : Fin (Fintype.card M)) :
      Function.Bijective (algebraMap (Localization.AtPrime (q i).1.asIdeal)
        (Ideal.ResidueField (q i).1.asIdeal)) := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue,
      ← Localization.AtPrime.map_eq_maximalIdeal, hzero]
  have havoid (i : Fin (Fintype.card M)) (s : R) (hs : s ∈ nonZeroDivisors R) :
      s ∉ (q i).1.asIdeal := by
    exact fun hp ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hp (q i).2 hs
  have hmaps (i : Fin (Fintype.card M)) :
      ∃! φ : FractionRing R →+* Localization.AtPrime (q i).1.asIdeal,
        φ.comp (algebraMap R (FractionRing R)) =
          algebraMap R (Localization.AtPrime (q i).1.asIdeal) := by
    let hunit (s : nonZeroDivisors R) :
        IsUnit (algebraMap R (Localization.AtPrime (q i).1.asIdeal) s) :=
      IsLocalization.map_units _ (⟨s.1, havoid i s.1 s.2⟩ : (q i).1.asIdeal.primeCompl)
    refine ⟨IsLocalization.lift hunit, IsLocalization.lift_comp hunit, ?_⟩
    intro ψ hψ
    exact IsLocalization.ringHom_ext (nonZeroDivisors R)
      (hψ.trans (IsLocalization.lift_comp hunit).symm)
  refine ⟨Fintype.card M, q, hfield, hzero, hres, havoid, hmaps, ?_⟩
  intro φ hφ
  exact fractionRing_pi_bijective_of_compatible φ hφ
