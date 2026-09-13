/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smooth algebras over a regular ring are regular

Regularity of a ring is a condition on its localisations at primes, and a smooth algebra is
standard smooth after inverting a single element outside any given prime.  So the statement that
a standard smooth algebra over a regular ring is regular upgrades at once to smooth algebras.

## Main results

* `Algebra.Smooth.isRegularRing`: a smooth algebra over a regular ring is a regular ring.
-/

@[expose] public section

namespace Algebra

/-- **A smooth algebra over a regular ring is regular.** -/
theorem Smooth.isRegularRing {R S : Type*} [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  rw [isRegularRing_iff]
  intro 𝔮 h𝔮
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R 𝔮
  have hdisj : Disjoint (Submonoid.powers g : Set S) (𝔮 : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg
  have : IsRegularRing (Localization.Away g) := Algebra.IsStandardSmooth.isRegularRing (R := R)
  -- `𝔮` survives as a prime `P` of `S[1/g]`, and `S_𝔮` is the localisation of `S[1/g]` at `P`
  set P := 𝔮.map (algebraMap S (Localization.Away g))
  have : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ 𝔮 h𝔮 hdisj
  have hunder : P.under S = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers g) _ h𝔮 hdisj
  have : IsRegularLocalRing (Localization.AtPrime P) :=
    IsRegularRing.isRegularLocalRing_localization P
  have hpc : 𝔮.primeCompl = (P.under S).primeCompl := by
    ext x
    simp [Ideal.mem_primeCompl_iff, hunder]
  have hloc : IsLocalization 𝔮.primeCompl (Localization.AtPrime P) := by
    rw [hpc]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime P)
    (IsLocalization.algEquiv 𝔮.primeCompl _ (Localization.AtPrime 𝔮)).toRingEquiv

end Algebra
