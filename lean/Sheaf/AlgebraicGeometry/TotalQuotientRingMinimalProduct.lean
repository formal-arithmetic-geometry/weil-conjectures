/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Total quotient ring as a product over minimal primes

Source: literature/stacks-project/algebra.tex, Algebra Lemma 10.25.4, tag 02LX,
with Definition 10.66.1, tag 0547, and Lemma 10.66.7, tag 05C3
(blueprint: lem-sc-affine-totalquotient-minimal-product)
-/

@[expose] public section

universe u

namespace Algebra

/-- The canonical total quotient ring decomposition for finitely many minimal primes,
when every weakly associated prime is minimal. The equivalence `q` enumerates all
minimal primes exactly once. The colon ideal `(⊥ : Submodule A A).colon {a}` is the
annihilator `{r | r * a = 0}` of `a`, and weak association is membership in its minimal
primes, as in `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`. Thus `hweak` states
the weak-association hypothesis of Definition 10.66.1 (tag 0547), without an
unspecified predicate. An `A`-algebra equivalence necessarily sends each fraction to
its images in the prime localizations: it fixes the images of numerators and maps
inverses of denominators to inverses.

Source: literature/stacks-project/algebra.tex, Algebra Lemma 10.25.4, tag 02LX,
with Definition 10.66.1, tag 0547, and Lemma 10.66.7, tag 05C3
(blueprint: lem-sc-affine-totalquotient-minimal-product)

Proof:
1. By `lem-sc-affine-weakass-nonzerodivisors`, zero-divisors form the union of the
weakly associated primes. By `hweak` and `lem-pc-minimal-prime-avoids-nonzerodivisor`,
this is exactly the union of the minimal primes. Non-zero-divisors avoid every factor's prime.
2. The localization universal property (`def-weil-pbc-module-localization` and
`def-weil-pbc-localization-at-prime`) gives the canonical map to each factor and their product.
3. By `lem-weil-pbc-localization-prime-residue-field-iso`, primes of the total quotient
ring correspond to primes disjoint from non-zero-divisors. By
`lem-weil-pbc-prime-avoidance` and minimality, these are exactly the listed primes;
minimality also shows that their extensions are maximal.
4. By `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, their intersection is the nilradical,
so every element of the Jacobson radical is nilpotent. Apply
`lem-weil-pbc-product-of-localizations-at-maximal` to obtain the product decomposition.
5. By `lem-weil-pbc-localization-prime-residue-field-iso`, the factors identify with
`A` localized at the corresponding minimal primes, compatibly with the maps from `A`.
Uniqueness in step 2 identifies the resulting equivalence with the canonical map. -/
theorem totalQuotientRing_isProduct_minimalPrimes
    {A : Type u} [CommRing A] {t : ℕ}
    (q : Fin t ≃ {p : PrimeSpectrum A // p.asIdeal ∈ minimalPrimes A})
    (hweak : ∀ (a : A) (p : Ideal A),
      p ∈ ((⊥ : Submodule A A).colon {a}).minimalPrimes →
        p ∈ minimalPrimes A) :
    Nonempty (Localization (nonZeroDivisors A) ≃ₐ[A]
      (∀ i : Fin t, Localization.AtPrime (q i).val.asIdeal)) := by
  classical
  let S := nonZeroDivisors A
  let Q := Localization S
  let s : Finset (Ideal A) := Finset.univ.image (fun i : Fin t ↦ (q i).val.asIdeal)
  have hs (p : Ideal A) : p ∈ s ↔ p ∈ minimalPrimes A := by
    constructor
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact (q i).property
    · intro hp
      obtain ⟨i, hi⟩ := q.surjective ⟨⟨p, hp.isPrime⟩, hp⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        congrArg (fun r ↦ r.val.asIdeal) hi⟩
  -- A zero-divisor lies in a prime minimal over a nonzero element's annihilator.
  have hminimal (p : Ideal A) [p.IsPrime]
      (hd : Disjoint (S : Set A) (p : Set A)) : p ∈ minimalPrimes A := by
    have hsub : (p : Set A) ⊆ ⋃ r ∈ (↑s : Set (Ideal A)), (r : Set A) := by
      intro x hx
      have hn : x ∉ nonZeroDivisors A := fun h ↦ Set.disjoint_left.mp hd h hx
      obtain ⟨y, hxy, hy⟩ := notMem_nonZeroDivisors_iff_left.mp hn
      have hproper : (⊥ : Submodule A A).colon {y} ≠ ⊤ := by
        intro htop
        have hmem : (1 : A) ∈ (⊥ : Submodule A A).colon {y} := by rw [htop]; trivial
        have hz : y = 0 := by simpa [Submodule.mem_colon_singleton] using hmem
        exact hy hz
      obtain ⟨⟨r, hr⟩⟩ := Ideal.nonempty_minimalPrimes hproper
      have hxann : x ∈ (⊥ : Submodule A A).colon {y} := by
        simpa [Submodule.mem_colon_singleton, mul_comm] using hxy
      exact Set.mem_iUnion₂.mpr ⟨r, (hs r).mpr (hweak y r hr), hr.le hxann⟩
    obtain ⟨r, hr, hpr⟩ :=
      (Ideal.subset_union_prime (s := s) (f := fun r ↦ r) (I := p) ⊥ ⊥
        (fun r hr _ _ ↦ ((hs r).mp hr).isPrime)).mp hsub
    have hm := (hs r).mp hr
    have heq : p = r := hpr.antisymm (hm.2 ⟨inferInstance, bot_le⟩ hpr)
    exact heq ▸ hm
  -- Prime avoidance makes the localization spectrum exactly the minimal primes.
  let E : PrimeSpectrum Q ≃
      {p : PrimeSpectrum A // p.asIdeal ∈ minimalPrimes A} :=
    (IsLocalization.primeSpectrumOrderIso S Q).toEquiv.trans
      { toFun := fun p ↦ ⟨p.val, hminimal _ p.property⟩
        invFun := fun p ↦
          ⟨p.val, (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.property).symm⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  let e : Fin t ≃ PrimeSpectrum Q := q.trans E.symm
  have hcomap (i : Fin t) :
      (e i).asIdeal.comap (algebraMap A Q) = (q i).val.asIdeal := by
    exact congrArg (fun p ↦ p.val.asIdeal) (E.apply_symm_apply (q i))
  have hfinite : Finite (PrimeSpectrum Q) := Finite.of_equiv (Fin t) e
  -- Inclusions between these contracted minimal primes must be equalities.
  have hdim : Ring.KrullDimLE 0 Q := by
    apply Ring.KrullDimLE.mk₀
    intro p hp
    obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
    have hpmin := (E ⟨p, hp⟩).property
    have hmmin := (E ⟨m, hm.isPrime⟩).property
    have hle := Ideal.comap_mono (f := algebraMap A Q) hpm
    have heq : p = m := (IsLocalization.orderEmbedding S Q).injective
      (hle.antisymm (hmmin.2 ⟨hpmin.isPrime, bot_le⟩ hle))
    exact heq ▸ hm
  let : DiscreteTopology (PrimeSpectrum Q) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨hfinite, hdim⟩
  -- Identify the factors before reindexing the canonical product equivalence.
  have hloc (i : Fin t) :
      IsLocalization.AtPrime (Localization.AtPrime (e i).asIdeal) (q i).val.asIdeal := by
    simpa only [hcomap i] using
      (IsLocalization.prime_localRing_residueField_iso A Q S (e i).asIdeal).2.2.2.2.2.1
  let F (i : Fin t) : Localization.AtPrime (e i).asIdeal ≃ₐ[A]
      Localization.AtPrime (q i).val.asIdeal := by
    let := hloc i
    exact IsLocalization.algEquiv (q i).val.asIdeal.primeCompl _ _
  exact ⟨((PrimeSpectrum.toPiLocalizationEquiv Q).restrictScalars A).trans
    (((AlgEquiv.piCongrLeft A (fun p : PrimeSpectrum Q ↦ Localization.AtPrime p.asIdeal)
      e).symm).trans (AlgEquiv.piCongrRight F))⟩

end Algebra
