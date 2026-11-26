/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.RingTheory.LocalizedFiniteQuotientCharts
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite quotient comparison for a localized finite algebra

For a finite algebra `S` over a Noetherian ring `R`, a prime `p`, `B = R_p ⊗[R] S` and
`J = pB`, the quotient `B ⧸ J^n` is the product of the quotients `S_q ⧸ K_q^n` over the primes
`q` above `p`, where `K_q = J S_q` is cofinal with the maximal ideal of `S_q`.

## Implementation details

Since `q` is minimal over `pS` by incomparability, `K_q` has radical the maximal ideal of
`S_q`, which gives cofinality. For `n > 0`, `B ⧸ J^n` is finite over the Artinian local ring
`R_p ⧸ m^n`, so it has discrete spectrum and is the product of its localizations at maximal
ideals; these are identified with the `S_q ⧸ K_q^n` by the local-chart lemma.

## References

* [Stacks, Tag 07N9], second equality
* [Stacks, Tag 00JA]
* [Stacks, Tag 00KH]
* [Stacks, Tag 00CT]
* [Stacks, Tag 0394]
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- A positive maximal-ideal-power quotient of a finite algebra has discrete spectrum. -/
private theorem finite_local_quotient_discrete
    (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B]
    (n : ℕ) (hn : n ≠ 0) :
    DiscreteTopology
      (PrimeSpectrum (B ⧸ ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A B))) := by
  let m := IsLocalRing.maximalIdeal A
  have : m.IsPrime := inferInstance
  have hmin : m ∈ (m ^ n).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hn,
      Ideal.IsPrime.radical (inferInstance : m.IsPrime), Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have : IsArtinianRing (A ⧸ m ^ n) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  let C := B ⧸ (m ^ n).map (algebraMap A B)
  let : Algebra (A ⧸ m ^ n) C :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower A (A ⧸ m ^ n) C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite (A ⧸ m ^ n) C :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact Algebra.QuasiFinite.discreteTopology_primeSpectrum (A ⧸ m ^ n) C

/-- The algebraic finite-quotient comparison for a localized finite algebra: for maps
`ψ q : B → S_q` extending the local maps, each `K_q = J S_q` lies between a power of the
maximal ideal of `S_q` and that maximal ideal, and for every `n` the induced map
`B ⧸ J^n → ∏ q, S_q ⧸ K_q^n` is bijective. -/
theorem completion_localizedAlgebra_finite_quotients
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1),
      (∀ (q : Q) (r : A), ψ q (r ⊗ₜ[R] (1 : S)) =
        Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) r) →
      let K := fun q : Q ↦ J.map (ψ q).toRingHom
      (∀ q : Q, K q ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q.1) ∧
        ∃ c : ℕ, 1 ≤ c ∧
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ c ≤ K q) ∧
      ∀ n : ℕ, Function.Bijective
        (RingHom.pi (fun q : Q ↦
          Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
            rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])) :
          (B ⧸ J ^ n) →+* (∀ q : Q, Localization.AtPrime q.1 ⧸ (K q) ^ n)) := by
  classical
  dsimp only
  let A := Localization.AtPrime p
  let B := A ⊗[R] S
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let J := p.map (algebraMap R B)
  intro ψ hψ
  let K := fun q : p.primesOver S ↦ J.map (ψ q).toRingHom
  have hcomp (q : p.primesOver S) :
      RingHom.comp (ψ q : B →+* Localization.AtPrime q.1)
        (algebraMap R B) =
        (algebraMap S (Localization.AtPrime q.1)).comp (algebraMap R S) := by
    ext r
    change ψ q (algebraMap R A r ⊗ₜ[R] 1) = _
    rw [hψ]
    exact Localization.localRingHom_to_map p q.1 (algebraMap R S)
      (Ideal.LiesOver.over (P := q.1) (p := p)) r
  have hK (q : p.primesOver S) : K q =
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q.1)) := by
    dsimp [K, J]
    rw [Ideal.map_map, hcomp, Ideal.map_map]
  constructor
  · intro q
    change K q ≤ _ ∧ ∃ c : ℕ, 1 ≤ c ∧ _ ≤ K q
    refine ⟨?_, ?_⟩
    · rw [hK q, ← IsLocalization.AtPrime.map_eq_maximalIdeal q.1]
      apply Ideal.map_mono
      rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq (Ideal.LiesOver.over (P := q.1) (p := p))
    have hmin : q.1 ∈ (p.map (algebraMap R S)).minimalPrimes := by
      simpa only [← Ideal.over_def q.1 p] using
        (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) q.1)
    have hrad : (K q).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.1) := by
      rw [hK q,
        IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
          (A := Localization.AtPrime q.1) q.1 _ hmin,
        IsLocalization.AtPrime.map_eq_maximalIdeal]
    let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (le_of_eq hrad.symm) (Ideal.fg_of_isNoetherianRing _)
    refine ⟨max 1 c, le_max_left _ _, ?_⟩
    exact (Ideal.pow_le_pow_right (le_max_right 1 c)).trans hc
  · intro n
    by_cases hn : n = 0
    · subst n
      have : Subsingleton (B ⧸ J ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      have (q : p.primesOver S) : Subsingleton (Localization.AtPrime q.1 ⧸ (K q) ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · have hJ : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = J := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
        rfl
      have : DiscreteTopology (PrimeSpectrum (B ⧸ J ^ n)) := by
        rw [← hJ, ← Ideal.map_pow]
        exact finite_local_quotient_discrete A B n hn
      let C := B ⧸ J ^ n
      let T := fun q : p.primesOver S ↦ Localization.AtPrime q.1 ⧸ (K q) ^ n
      let f (q : p.primesOver S) : C →+* T q :=
        Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
          rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])
      obtain ⟨e, _, he⟩ := localized_finite_quotient_charts R S p ψ n hn
      let (q : p.primesOver S) : Algebra C (T q) := (f q).toAlgebra
      have (q : p.primesOver S) : IsLocalization.AtPrime (T q) (e q).asIdeal := he q
      let E (q : p.primesOver S) := IsLocalization.algEquiv (e q).asIdeal.primeCompl
        (Localization.AtPrime (e q).asIdeal) (T q)
      let F := (MaximalSpectrum.toPiLocalizationEquiv C).toRingEquiv
      let G := RingEquiv.piCongrLeft'
        (fun m : MaximalSpectrum C ↦ Localization.AtPrime m.asIdeal) e.symm
      let H := RingEquiv.piCongrRight (fun q ↦ (E q).toRingEquiv)
      have hEq : RingHom.pi f = ((F.trans G).trans H).toRingHom := by
        apply RingHom.ext
        intro x
        funext q
        exact (E q).commutes x |>.symm
      change Function.Bijective (RingHom.pi f)
      rw [hEq]
      exact ((F.trans G).trans H).bijective

end AdicCompletion
