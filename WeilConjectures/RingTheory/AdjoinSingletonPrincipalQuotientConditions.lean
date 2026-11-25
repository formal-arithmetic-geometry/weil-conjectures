/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdjoinSingletonAssociatedLocalization
import WeilConjectures.RingTheory.AdjoinQuotientSurjective
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Principal-quotient conditions for a fractional monogenic algebra

Let `R` be a Noetherian Nagata normal domain with fraction field `K`, `0 ≠ x ∈ K`, and `m` a
maximal ideal of `R[x]` containing `x`. In `A = R[x]_m`, the image of `x` satisfies the three
hypotheses on associated primes of `A / (x)` used in the analytic-unramifiedness criterion.

## References

* [Stacks Project, Tag 0334], Step 5
* [Stacks Project, Tag 0330], [Stacks Project, Tag 031T], [Stacks Project, Tag 00PD]
-/

@[expose] public section

universe u v

/-- Transport the Nagata property through a ring isomorphism, viewed as a finite map. -/
private theorem nagata_of_equiv {B C : Type*} [CommRing B] [CommRing C]
    (e : B ≃+* C) (hB : IsNagataRing B) : IsNagataRing C := by
  let := e.toRingHom.toAlgebra
  have : Module.Finite B C := RingHom.Finite.of_surjective e.toRingHom e.surjective
  exact (finite_over_nagata_is_nagata B C hB).1

/-- A prime quotient of the local monogenic algebra in which the generator dies is Nagata. -/
private theorem adjoin_local_quotient_nagata (R : Type u) (K : Type v)
    [CommRing R] [CommRing K] [Algebra R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsPrime]
    (p : Ideal (Localization.AtPrime m))
    (hx : algebraMap (Algebra.adjoin R ({x} : Set K)) (Localization.AtPrime m)
      ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ ∈ p) :
    IsNagataRing (Localization.AtPrime m ⧸ p) := by
  let S := Algebra.adjoin R ({x} : Set K)
  let A := Localization.AtPrime m
  let q : Ideal S := p.under S
  have hsurj : Function.Surjective (algebraMap R (S ⧸ q)) :=
    adjoin_quotient_surjective R K ({x} : Set K) q
      (fun y hy ↦ by obtain rfl := Set.mem_singleton_iff.mp hy; exact hx)
  have : Module.Finite R (S ⧸ q) :=
    Module.Finite.of_surjective (Algebra.linearMap R (S ⧸ q)) hsurj
  have hq : IsNagataRing (S ⧸ q) := (finite_over_nagata_is_nagata R (S ⧸ q) hR).1
  let T := Algebra.algebraMapSubmonoid (S ⧸ q) m.primeCompl
  have hloc := (isNagataRing_localization (S ⧸ q) T hq).1
  have heq : q.map (algebraMap S A) = p := IsLocalization.map_under m.primeCompl A p
  have hcanonical : IsNagataRing (A ⧸ q.map (algebraMap S A)) :=
    nagata_of_equiv (IsLocalization.algEquiv T (Localization T)
      (A ⧸ q.map (algebraMap S A))).toRingEquiv hloc
  exact nagata_of_equiv (Ideal.quotEquivOfEq heq) hcanonical

/-- Let `R` be a Noetherian Nagata normal domain with fraction field `K`, `0 ≠ x ∈ K` with `R[x]`
Noetherian, and `m` a maximal ideal of `R[x]` containing `x`. Let `A = R[x]_m` and `t` the image
of `x`. Every associated prime `p` of `A / (t)` is minimal over `(t)`, the localization `A_p` is a
regular local ring, and `p` is analytically unramified. -/
theorem adjoin_singleton_atPrime_principal_quotient_conditions
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsNagataRing R) (x : K) (hx0 : x ≠ 0)
    [IsNoetherianRing (Algebra.adjoin R ({x} : Set K))]
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hx : (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
      Algebra.adjoin R ({x} : Set K)) ∈ m) :
    let A := Localization.AtPrime m
    let t : A := algebraMap (Algebra.adjoin R ({x} : Set K)) A
      ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
    (∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {t}), (Ideal.span {t}).IsMinimalPrime p) ∧
    (∀ p : associatedPrimes A (A ⧸ Ideal.span {t}),
      IsRegularLocalRing (Localization.AtPrime p.1)) ∧
    (∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {t}), p.IsAnalyticallyUnramified) := by
  dsimp only
  let S := Algebra.adjoin R ({x} : Set K)
  let A := Localization.AtPrime m
  let tS : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  let t : A := algebraMap S A tS
  have htS : tS ≠ 0 := fun h ↦ hx0 (congrArg (fun z : S ↦ (z : K)) h)
  have ht : t ≠ 0 := fun h ↦ htS
    ((IsLocalization.injective A m.primeCompl_le_nonZeroDivisors)
      (by simpa only [map_zero] using h))
  have hlocal (p : associatedPrimes A (A ⧸ Ideal.span {t})) :
      p.1.height = 1 ∧ IsRegularLocalRing (Localization.AtPrime p.1) := by
    obtain ⟨q, hq, hheight, ⟨e⟩⟩ := adjoin_singleton_associated_localization R K x hx0 m hx p
    let : q.IsPrime := hq
    have hdimq : ringKrullDim (Localization.AtPrime q) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hheight]
      rfl
    have hdim : ringKrullDim (Localization.AtPrime p.1) = 1 :=
      e.ringKrullDim.trans hdimq
    have hpheight : p.1.height = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1] at hdim
      exact_mod_cast hdim
    let : IsIntegrallyClosed (Localization.AtPrime q) :=
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
    let : IsRegularLocalRing (Localization.AtPrime q) :=
      IsRegularLocalRing.of_isIntegrallyClosed _ hdimq.le
    exact ⟨hpheight, IsRegularLocalRing.of_ringEquiv e.symm⟩
  have hle (p : Ideal A) (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {t})) :
      Ideal.span {t} ≤ p := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using hp.annihilator_le
  refine ⟨?_, fun p ↦ (hlocal p).2, ?_⟩
  · intro p hp
    let : p.IsPrime := hp.isPrime
    refine ⟨⟨inferInstance, hle p hp⟩, ?_⟩
    intro q hq hqp
    let : q.IsPrime := hq.1
    by_contra hpq
    have hlt : q < p := lt_of_le_not_ge hqp hpq
    have hqbot : q ≠ ⊥ := by
      intro heq
      have hmem : t ∈ q := hq.2 (Ideal.subset_span (Set.mem_singleton t))
      exact ht (by simpa [heq] using hmem)
    have hqheight : 1 ≤ q.height := Order.one_le_iff_ne_zero.mpr
      (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqbot)
    have hbad := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [(hlocal ⟨p, hp⟩).1] at hbad
    have htwo : (2 : ℕ∞) ≤ q.height + 1 := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ q.height + 1 := add_le_add hqheight le_rfl
    have : (2 : ℕ∞) ≤ 1 := htwo.trans hbad
    norm_num at this
  · intro p hp
    let : p.IsPrime := hp.isPrime
    have hxp : t ∈ p := hle p hp (Ideal.subset_span (Set.mem_singleton t))
    let : IsLocalRing (Localization.AtPrime m ⧸ p) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    refine ⟨inferInstance, ?_⟩
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact isAnalyticallyUnramified_of_isNagataRing _
      (adjoin_local_quotient_nagata R K hR x m p hxp)
