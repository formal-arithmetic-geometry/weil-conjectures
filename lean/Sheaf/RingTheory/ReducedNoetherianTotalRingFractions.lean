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
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Total ring of fractions of a reduced Noetherian ring

Source: literature/stacks-project/algebra.tex, Lemma Tag 02LX (blueprint:
lem-weil-pbc-reduced-noetherian-total-ring-fractions).
-/

@[expose] public section

universe u

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
  sorry
