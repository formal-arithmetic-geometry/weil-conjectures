/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: N5
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Boundary-unit factorization in a regular local ring

Source: Stacks Project, more-algebra.tex, Tag 0AG0, lemma-regular-local-UFD
(blueprint: lem-trf-regular-local-ufd-boundary-factorization).
-/

@[expose] public section

open scoped BigOperators

universe u

private theorem parameter_prime (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (t : List A) (ht : IsLocalRing.IsRegularSystemOfParameters t) (i : Fin t.length) :
    Prime (t.get i) := by
  let ys := t.get i :: t.eraseIdx i.val
  have hperm : t.Perm ys := (List.getElem_cons_eraseIdx_perm i.isLt).symm
  have hmain := IsRegularLocalRing.isRegular_and_quotients_of_generators
    A t.length ht.2.symm t ht
  have hys := (hmain.2.2 ys hperm).1
  have hreg := (hmain.2.2 ys hperm).2
  have hx : t.get i ≠ 0 := by
    intro hzero
    have hsmul := (RingTheory.Sequence.isRegular_cons_iff A _ _).mp hreg |>.1
    rw [hzero] at hsmul
    exact IsSMulRegular.not_zero (M := A) hsmul
  have hquot := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    A t.length ht.2.symm ys hys).2.1 1 (by have := i.isLt; omega) |>.1
  have heq : Ideal.ofList (ys.take 1) = Ideal.span {t.get i} := by
    simp [ys, Ideal.ofList]
  rw [heq] at hquot
  exact (Ideal.span_singleton_prime hx).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)

private theorem factorization_of_localized_unit (A : Type u) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {r : ℕ} (t : Fin r → A) (ht : ∀ i, Prime (t i))
    (f : A) :
    IsUnit (algebraMap A (Localization.Away (∏ i, t i)) f) ↔
      ∃ u : A, IsUnit u ∧ ∃ a : Fin r → ℕ, f = u * ∏ i, t i ^ a i := by
  classical
  let T := ∏ i, t i
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (ht i).ne_zero)
  constructor
  · induction f using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro h
      obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff T).mp h
      exact False.elim ((pow_ne_zero n hT) (zero_dvd_iff.mp hn))
    | h₂ f hf =>
      intro _
      exact ⟨f, hf, fun _ ↦ 0, by simp⟩
    | h₃ f p _ hp ih =>
      intro h
      have hmul : IsUnit (algebraMap A (Localization.Away T) p) ∧
          IsUnit (algebraMap A (Localization.Away T) f) := by
        simpa only [map_mul, IsUnit.mul_iff] using h
      obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff T).mp hmul.1
      obtain ⟨i, _, hi⟩ := hp.exists_mem_finset_dvd (hp.dvd_of_dvd_pow hn)
      obtain ⟨v, hv⟩ := (hp.associated_of_dvd (ht i) hi).symm
      obtain ⟨u, hu, a, ha⟩ := ih hmul.2
      refine ⟨(v : A) * u, v.isUnit.mul hu,
        fun j ↦ a j + if j = i then 1 else 0, ?_⟩
      simp only [pow_add, pow_ite, pow_one, pow_zero, Finset.prod_mul_distrib,
        Finset.prod_ite_eq', Finset.mem_univ, if_true]
      rw [← hv, ha]
      ac_rfl
  · rintro ⟨u, hu, a, rfl⟩
    rw [map_mul, map_prod]
    refine (hu.map _).mul (IsUnit.prod_iff.mpr (fun i _ ↦ ?_))
    rw [map_pow]
    exact (IsLocalization.Away.isUnit_of_dvd T
      (Finset.dvd_prod_of_mem t (Finset.mem_univ i))).pow _

/-- A regular local ring is a domain and a UFD; selected members of a regular parameter
system are prime, and they are exactly the possible non-unit factors after inverting their
product. Source: Stacks Project, more-algebra.tex, Tag 0AG0, lemma-regular-local-UFD
(blueprint: lem-trf-regular-local-ufd-boundary-factorization).

Proof: use the regular-local domain theorem and the regular-parameter hypersurface criterion to
show that each selected parameter is prime. Induct on the dimension, localizing at a parameter
and applying the regular-local UFD induction hypothesis, then descend primality with Nagata's
criterion to obtain `UniqueFactorizationMonoid A`. In that UFD, a unit in the localization at the
product has no prime factors except the selected parameters, giving the displayed factorization;
the converse follows by choosing a common denominator. The argument permits `r = 0`, when the
product is `1` and the assertion reduces to being a unit in `A`.
-/
theorem regularLocalUFDBoundaryFactorization (A : Type u) [CommRing A]
    [IsRegularLocalRing A]
    (t : List A) (ht : IsLocalRing.IsRegularSystemOfParameters t)
    (r : ℕ) (ι : Fin r → Fin t.length) (hι : Function.Injective ι) :
    IsDomain A ∧ UniqueFactorizationMonoid A ∧
      (∀ i : Fin r, Prime (t.get (ι i))) ∧
      (∀ f : A,
        IsUnit (algebraMap A (Localization.Away (∏ i : Fin r, t.get (ι i))) f) ↔
          ∃ u : A, IsUnit u ∧ ∃ a : Fin r → ℕ,
            f = u * ∏ i : Fin r, (t.get (ι i)) ^ (a i)) := by
  have _ := hι
  have : IsRegularRing A :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal A)).2
  have : UniqueFactorizationMonoid A := IsRegularLocalRing.uniqueFactorizationMonoid A
  have hp : ∀ i : Fin r, Prime (t.get (ι i)) := fun i ↦ parameter_prime A t ht (ι i)
  exact ⟨inferInstance, inferInstance, hp,
    factorization_of_localized_unit A (fun i ↦ t.get (ι i)) hp⟩

end
