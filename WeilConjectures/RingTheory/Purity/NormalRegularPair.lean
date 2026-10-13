/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Parameters of the base form a regular pair on a normal finite extension

Let `(A, 𝔪)` be a Noetherian integrally closed local domain with `ht 𝔪 ≥ 2`, and let `x, y ∈ A`
with `x ≠ 0` and `𝔪 ⊆ √(x, y)`. If `B` is a Noetherian integrally closed domain which is an
integral extension of `A`, then `[x, y]` is a weakly regular sequence on `B`
(`IsIntegrallyClosed.isWeaklyRegular_pair_of_isIntegral`).

The key point is `IsIntegrallyClosed.exists_eq_of_mul_maximalIdeal`: in a Noetherian integrally
closed local domain `R` whose maximal ideal `𝔫` is not principal, an element `f` of the fraction
field with `f 𝔫 ⊆ R` lies in `R` (either `f 𝔫 ⊆ 𝔫` and `f` is integral, or `f 𝔫 = R` and
`𝔫 = f⁻¹ R` is principal). Applied to the localizations of `B` at its maximal ideals (which have
height at least two by going down) this shows that the maximal ideals of `B` are not associated to
`B / xB`.

This is step (i) of the dimension two case of the Zariski–Nagata purity theorem [Stacks 0BMA],
an input of blueprint `sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- By Krull's principal ideal theorem, the maximal ideal of a Noetherian local ring is not
principal as soon as it has height at least two. -/
lemma not_isPrincipal_maximalIdeal_of_two_le_height (h : 2 ≤ (maximalIdeal R).height) :
    ¬ (maximalIdeal R).IsPrincipal := by
  intro hp
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (maximalIdeal R)
    (maximalIdeal R) (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have := h.trans h1
  norm_num at this

end IsLocalRing

namespace IsIntegrallyClosed

variable {R K : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- In a Noetherian integrally closed local domain `R` with non-principal maximal ideal `𝔫`,
an element `f` of the fraction field with `f 𝔫 ⊆ R` lies in `R`. -/
theorem exists_eq_of_mul_maximalIdeal (hR : ¬ (maximalIdeal R).IsPrincipal) {f : K}
    (hf : ∀ m ∈ maximalIdeal R, ∃ r, algebraMap R K r = f * algebraMap R K m) :
    ∃ r, algebraMap R K r = f := by
  choose w hw using hf
  have hm0 : maximalIdeal R ≠ ⊥ := fun h0 ↦ hR ⟨⟨0, by simp [h0]⟩⟩
  by_cases hint : ∀ m (hm : m ∈ maximalIdeal R), w m hm ∈ maximalIdeal R
  · let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
    have hN : N ≠ ⊥ := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
      intro hN
      have : algebraMap R K y ∈ N := Submodule.mem_map_of_mem hy
      rw [hN, Submodule.mem_bot, IsFractionRing.to_map_eq_zero_iff] at this
      exact hy0 this
    have hint' : IsIntegral R f := by
      refine isIntegral_of_smul_mem_submodule N hN
        (Submodule.FG.map _ (maximalIdeal R).fg_of_isNoetherianRing) f fun n hn ↦ ?_
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
      rw [smul_eq_mul, Algebra.linearMap_apply, ← hw y hy]
      exact Submodule.mem_map_of_mem (hint y hy)
    exact IsIntegrallyClosed.isIntegral_iff.1 hint'
  · push Not at hint
    obtain ⟨m, hm, hwm⟩ := hint
    have hu : IsUnit (w m hm) := by
      by_contra hu
      exact hwm ((mem_maximalIdeal _).2 hu)
    exfalso
    refine hR ⟨⟨m, le_antisymm (fun z hz ↦ ?_) ?_⟩⟩
    · rw [Submodule.mem_span_singleton]
      refine ⟨w z hz * ↑hu.unit⁻¹, ?_⟩
      have : m * w z hz = z * w m hm := IsFractionRing.injective R K (by
        simp only [map_mul, hw]
        ring)
      calc (w z hz * ↑hu.unit⁻¹) • m = (m * w z hz) * ↑hu.unit⁻¹ := by
            rw [smul_eq_mul]; ring
        _ = z := by rw [this, mul_assoc, IsUnit.mul_val_inv, mul_one]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hm

omit [IsDomain R] in
/-- In a Noetherian integrally closed local domain `R` with non-principal maximal ideal `𝔫`,
an element `f` of the fraction field with `f 𝔫ⁿ ⊆ R` lies in `R`. -/
theorem exists_eq_of_mul_maximalIdeal_pow (hR : ¬ (maximalIdeal R).IsPrincipal) (n : ℕ)
    {f : K} (hf : ∀ m ∈ maximalIdeal R ^ n, ∃ r, algebraMap R K r = f * algebraMap R K m) :
    ∃ r, algebraMap R K r = f := by
  induction n generalizing f with
  | zero => simpa using hf 1 (by simp)
  | succ n ih =>
    refine ih fun g hg ↦ exists_eq_of_mul_maximalIdeal hR fun m hm ↦ ?_
    obtain ⟨r, hr⟩ := hf (g * m) (by rw [pow_succ]; exact Ideal.mul_mem_mul hg hm)
    exact ⟨r, by rw [hr, map_mul, mul_assoc]⟩

variable (R) in
/-- In a Noetherian integrally closed local domain `R` with non-principal maximal ideal, let
`a ≠ 0` and `c` be such that `(a, c)` is primary to the maximal ideal. Then `c` is a
nonzerodivisor modulo `a`: if `a ∣ c b` then `a ∣ b`. -/
theorem dvd_of_dvd_mul_of_le_radical (hR : ¬ (maximalIdeal R).IsPrincipal) {a b c : R}
    (ha : a ≠ 0) (hc : maximalIdeal R ≤ (Ideal.span {a, c}).radical) (hcb : a ∣ c * b) :
    a ∣ b := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hc
    (maximalIdeal R).fg_of_isNoetherianRing
  obtain ⟨d, hd⟩ := hcb
  let K := FractionRing R
  have ha' : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha
  have hd' : algebraMap R K c * algebraMap R K b = algebraMap R K a * algebraMap R K d := by
    rw [← map_mul, ← map_mul, hd]
  obtain ⟨z, hz⟩ := exists_eq_of_mul_maximalIdeal_pow (K := K) hR n
    (f := algebraMap R K b / algebraMap R K a) fun m hm ↦ by
      obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 (hn hm)
      refine ⟨u * b + v * d, ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff ha']
      simp only [map_add, map_mul]
      linear_combination -(algebraMap R K v) * hd'
  refine ⟨z, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hz, mul_comm, div_mul_cancel₀ _ ha']


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
  [IsNoetherianRing A] [IsIntegrallyClosed A] [IsDomain B] [IsNoetherianRing B]
  [IsIntegrallyClosed B]
  [FaithfulSMul A B] [Algebra.IsIntegral A B]

omit [IsIntegrallyClosed B] in
/-- By going down, a maximal ideal of an integral extension `B` of a local integrally closed
domain `(A, 𝔪)` has height at least the height of `𝔪`. -/
theorem height_maximalIdeal_le_height (Q : Ideal B) [Q.IsMaximal] :
    (maximalIdeal A).height ≤ Q.height := by
  have : Q.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)).symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) Q]
  exact le_self_add

/-- Let `(A, 𝔪)` be an integrally closed local domain with `ht 𝔪 ≥ 2`, and `x, y ∈ A` with `x ≠ 0`
and `𝔪 ⊆ √(x, y)`. Then `[x, y]` is a weakly regular sequence on every Noetherian integrally
closed domain `B` which is an integral extension of `A`. Step (i) of [Stacks 0BMA] in dimension
two. -/
theorem isWeaklyRegular_pair_of_isIntegral {x y : A} (hx : x ≠ 0)
    (hm : maximalIdeal A ≤ (Ideal.span {x, y}).radical) (h2 : 2 ≤ (maximalIdeal A).height) :
    IsWeaklyRegular B [x, y] := by
  set X := algebraMap A B x
  set Y := algebraMap A B y
  have hinj := FaithfulSMul.algebraMap_injective A B
  have hX : X ≠ 0 := (map_ne_zero_iff _ hinj).2 hx
  -- the key point: `Y` is a nonzerodivisor modulo `X`
  have key : ∀ b : B, X ∣ Y * b → X ∣ b := by
    intro b hb
    by_contra hnot
    let J : Ideal B :=
      { carrier := {r | X ∣ r * b}
        add_mem' := fun {r s} hr hs ↦ by
          simp only [Set.mem_ofPred_eq, add_mul] at hr hs ⊢
          exact dvd_add hr hs
        zero_mem' := by simp
        smul_mem' := fun c r hr ↦ by
          simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_assoc] at hr ⊢
          exact dvd_mul_of_dvd_right hr c }
    have hJ : J ≠ ⊤ := fun h ↦ hnot (by
      have : (1 : B) ∈ J := h ▸ Submodule.mem_top
      simpa [J] using this)
    obtain ⟨Q, hQ, hJQ⟩ := Ideal.exists_le_maximal J hJ
    let R := Localization.AtPrime Q
    have hle := Ideal.primeCompl_le_nonZeroDivisors Q
    have : IsDomain R := IsLocalization.isDomain_localization hle
    have : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R Q.primeCompl hle
    have hRinj : Function.Injective (algebraMap B R) := IsLocalization.injective R hle
    have hcomap : (maximalIdeal R).comap (algebraMap B R) = Q :=
      Localization.AtPrime.under_maximalIdeal
    have hR : ¬ (maximalIdeal R).IsPrincipal := by
      refine IsLocalRing.not_isPrincipal_maximalIdeal_of_two_le_height ?_
      rw [← IsLocalization.height_under Q.primeCompl, Ideal.under, hcomap]
      exact h2.trans (height_maximalIdeal_le_height Q)
    have hQA : Q.comap (algebraMap A B) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
    have hrad : maximalIdeal R ≤ (Ideal.span {algebraMap B R X, algebraMap B R Y}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun P ⟨hP, hPp⟩ ↦ ?_
      have hPm : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal_of_isPrime P
      set P' := P.comap (algebraMap B R)
      have hP'Q : P' ≤ Q := by
        have := Ideal.comap_mono (f := algebraMap B R) hPm
        rwa [hcomap] at this
      have hspan : Ideal.span {x, y} ≤ P'.comap (algebraMap A B) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hP (Ideal.subset_span (by simp [X])), hP (Ideal.subset_span (by simp [Y]))⟩
      have hP'A : P'.comap (algebraMap A B) = maximalIdeal A :=
        le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
          (hm.trans ((Ideal.IsPrime.radical_le_iff inferInstance).2 hspan))
      have hP'eq : P' = Q := by
        by_contra hne
        have := Ideal.IsIntegral.comap_lt_comap (R := A) (lt_of_le_of_ne hP'Q hne)
        rw [hP'A, hQA] at this
        exact lt_irrefl _ this
      calc maximalIdeal R = Q.map (algebraMap B R) := Localization.AtPrime.map_eq_maximalIdeal.symm
        _ = P'.map (algebraMap B R) := by rw [hP'eq]
        _ ≤ P := (IsLocalization.map_under Q.primeCompl R P).le
    obtain ⟨z, hz⟩ := dvd_of_dvd_mul_of_le_radical R hR
      ((map_ne_zero_iff _ hRinj).2 hX) hrad (b := algebraMap B R b) (by
        obtain ⟨d, hd⟩ := hb
        exact ⟨algebraMap B R d, by rw [← map_mul, hd, map_mul]⟩)
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    have hbs : b * s = X * r := hRinj (by
      rw [map_mul, hz, map_mul, mul_assoc, IsLocalization.mk'_spec])
    have hsJ : (s : B) ∈ J := show X ∣ (s : B) * b from ⟨r, by rw [mul_comm, hbs]⟩
    exact s.2 (hJQ hsJ)
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨fun b₁ b₂ h ↦ mul_left_cancel₀ hX (by simpa only [Algebra.smul_def] using h), ?_⟩
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun q hq ↦ ?_
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hq
  obtain ⟨c, -, hc⟩ := hq
  obtain ⟨d, hd⟩ := key b ⟨c, by rw [← Algebra.smul_def, ← hc, Algebra.smul_def]⟩
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨d, Submodule.mem_top, by rw [Algebra.smul_def, hd]⟩

end IsIntegrallyClosed
