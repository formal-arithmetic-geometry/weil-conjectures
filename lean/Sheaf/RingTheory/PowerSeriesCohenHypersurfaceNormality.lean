/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.RingTheory.CohenRing
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingNormal

/-! # Normal power-series rings and Cohen hypersurfaces

Source: Stacks Project, Algebra, Tags 032C, 00NQ, 0AFS and 0567, and the node's
constant-coefficient argument (blueprint: lem-trf-power-series-cohen-hypersurface-normality).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPowerSeries

private theorem regular_of_field_or_cohen {A : Type*} [CommRing A] (d : ℕ)
    (hA : IsField A ∨ ∃ p : ℕ, IsCohenRing p A) :
    IsRegularLocalRing (MvPowerSeries (Fin d) A) := by
  rcases power_series_field_cohen_regular_complete d hA with
    ⟨_, _, _, _, _, _, _, _, hreg, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hreg, _⟩
  · exact hreg
  · exact hreg

private theorem normal_of_regular_local (A : Type*) [CommRing A]
    [IsRegularLocalRing A] : IsDomain A ∧ IsIntegrallyClosed A := by
  let m := IsLocalRing.maximalIdeal A
  have : IsRegularRing A :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing m).2
  obtain ⟨hdom, hnormal⟩ := IsRegularRing.isNormalRing A m
  let := hdom
  let := hnormal
  let e := (IsLocalization.atUnits A m.primeCompl
    (S := Localization.AtPrime m) (by
      intro a ha
      change IsUnit a
      by_contra h
      exact ha ((IsLocalRing.mem_maximalIdeal a).mpr h))).toRingEquiv
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem cohen_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (d p : ℕ) (hp : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      Ideal.span (insert (C (p : A)) (Set.range (X : Fin d → MvPowerSeries (Fin d) A))) := by
  have hk := (quotient_first_variables A d d le_rfl).2.2.2.2.1
  have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) =
      (IsLocalRing.maximalIdeal A).comap constantCoeff := by
    ext f
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  rw [hm]
  have hspan : Ideal.span (insert (C (p : A)) (Set.range (X : Fin d → _))) =
      (IsLocalRing.maximalIdeal A).map C ⊔ Ideal.span (Set.range (X : Fin d → _)) := by
    rw [hp, Ideal.map_span, Set.image_singleton, Ideal.span_insert]
  rw [hspan]
  apply le_antisymm
  · intro f hf
    have hdiff : f - C (constantCoeff f) ∈ RingHom.ker (constantCoeff (σ := Fin d)) := by
      simp
    rw [hk] at hdiff
    have hc := Ideal.mem_map_of_mem (C : A →+* MvPowerSeries (Fin d) A)
      (show constantCoeff f ∈ IsLocalRing.maximalIdeal A from hf)
    simpa using (Submodule.mem_sup.mpr ⟨_, hc, _, hdiff, add_sub_cancel _ _⟩)
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · rw [← hk]
      exact Ideal.comap_mono bot_le

/-- Power series over any field, and Cohen power series modulo a series with constant
coefficient exactly `p`, are regular local normal domains. The Cohen equation belongs
to `(p, X)` but not its square. The final conjunct in each case records the
zero-variable identification; no perfectness of the residue field is assumed.

Source: Stacks Project, Algebra, Tags 032C, 00NQ, 0AFS and 0567; the non-square
argument is the node's agent-origin constant-coefficient argument, using Tag 0327.
(blueprint: lem-trf-power-series-cohen-hypersurface-normality)

Proof:
1. Apply `lem-weil-pbc-power-series-field-cohen-regular-complete` to obtain regular
   localness of the field power-series ring and of the Cohen ambient ring, whose
   maximal ideal is `(p, X)`. This applies also to imperfect fields and zero variables.
2. By `lem-weil-pbc-power-series-quotient-variables`, constant coefficient is a ring
   homomorphism with kernel `(X)`. Thus the Cohen equation minus `p` lies in `(X)`
   and the equation lies in `(p, X)`. Constant coefficients of elements of this ideal
   lie in `pC`, so those of its square lie in `p²C`. But `p` does not lie in `p²C`:
   otherwise domain cancellation of the nonzero uniformizer would make `p` a unit,
   contradicting `def-weil-pbc-cohen-ring`. Hence the equation is outside the square.
3. Apply `lem-weil-pbc-regular-local-hypersurface-criterion` to the ambient regular
   local ring and this equation to obtain regular localness of the quotient.
4. By `lem-weil-pbc-regular-local-localization` each resulting ring is regular, and
   `lem-weil-pbc-regular-ring-normal` makes its maximal localization a normal domain.
   A local ring is isomorphic to its maximal localization: denominators outside the
   maximal ideal are units, and the inverse sends `a/s` to `a * s⁻¹`. Transporting
   along this isomorphism gives a nonzero domain and integral closedness in its
   fraction field, exactly `def-weil-pbc-normal-ring`.
5. For zero variables the constant-coefficient equivalence identifies the series
   ring with its coefficient ring (`def-weil-pbc-multivariate-power-series`). Thus
   the field case is `k`; in the Cohen case the equation is `p` and the quotient
   is `C/pC`. None of the steps assumes perfectness of `C/pC`. -/
theorem power_series_cohen_hypersurface_normality (d : ℕ) :
    (∀ (k : Type u) [Field k],
      IsRegularLocalRing (MvPowerSeries (Fin d) k) ∧
      IsDomain (MvPowerSeries (Fin d) k) ∧
      IsIntegrallyClosed (MvPowerSeries (Fin d) k) ∧
      (d = 0 → Nonempty (MvPowerSeries (Fin d) k ≃+* k))) ∧
    (∀ (C : Type v) [CommRing C] (p : ℕ), IsCohenRing p C →
      ∀ (Θ : MvPowerSeries (Fin d) C), constantCoeff Θ = (p : C) →
        Θ ∈ Ideal.span (insert (MvPowerSeries.C (p : C))
          (Set.range (X : Fin d → MvPowerSeries (Fin d) C))) ∧
        Θ ∉ Ideal.span (insert (MvPowerSeries.C (p : C))
          (Set.range (X : Fin d → MvPowerSeries (Fin d) C))) ^ 2 ∧
        IsRegularLocalRing (MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}) ∧
        IsDomain (MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}) ∧
        IsIntegrallyClosed (MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}) ∧
        (d = 0 → Nonempty ((MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}) ≃+*
          (C ⧸ Ideal.span {(p : C)})))) := by
  constructor
  · intro k _
    let := regular_of_field_or_cohen d (Or.inl (Field.toIsField k))
    obtain ⟨hdom, hnormal⟩ := normal_of_regular_local (MvPowerSeries (Fin d) k)
    refine ⟨inferInstance, hdom, hnormal, ?_⟩
    rintro rfl
    exact ⟨(isEmptyEquiv (Fin 0) k).toRingEquiv⟩
  · intro A _ p hA Θ hΘ
    have hcohen := hA
    obtain ⟨hprime, hdom, hdvr, hp, hcomplete⟩ := hA
    let := hdom
    let := hdvr
    let := regular_of_field_or_cohen d (Or.inr ⟨p, hcohen⟩)
    let n := Ideal.span (insert (C (p : A))
      (Set.range (X : Fin d → MvPowerSeries (Fin d) A)))
    have hm : IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) A) = n :=
      cohen_maximalIdeal d p hp
    have hn : n ≤ (Ideal.span {(p : A)}).comap constantCoeff := by
      apply Ideal.span_le.mpr
      rintro f (rfl | ⟨i, rfl⟩)
      · simp
      · simp
    have hmem : Θ ∈ n := by
      rw [← hm]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, hΘ]
      exact (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : A)).mpr hp |>.not_isUnit
    have hpow : n ^ 2 ≤ ((Ideal.span {(p : A)}) ^ 2).comap constantCoeff := by
      rw [pow_two, pow_two]
      apply Ideal.mul_le.mpr
      intro a ha b hb
      change constantCoeff (a * b) ∈ Ideal.span {(p : A)} * Ideal.span {(p : A)}
      rw [map_mul]
      exact Ideal.mul_mem_mul (hn ha) (hn hb)
    have hnmem : Θ ∉ n ^ 2 := by
      intro h
      have hc : (p : A) ∈ (Ideal.span {(p : A)}) ^ 2 := by
        simpa only [Ideal.mem_comap, hΘ] using hpow h
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc
      obtain ⟨a, ha⟩ := hc
      have hirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : A)).mpr hp
      have hcancel : (1 : A) = (p : A) * a := by
        apply mul_left_cancel₀ hirr.ne_zero
        simpa only [mul_one, pow_two, mul_assoc] using ha
      exact hirr.not_isUnit (isUnit_iff_dvd_one.mpr ⟨a, hcancel⟩)
    obtain ⟨hloc, hreg, _⟩ := IsRegularLocalRing.quotient_span_singleton
      (hm.symm ▸ hmem) (by simpa only [hm] using hnmem)
    let := hloc
    let := hreg
    obtain ⟨hqdom, hqnormal⟩ :=
      normal_of_regular_local (MvPowerSeries (Fin d) A ⧸ Ideal.span {Θ})
    refine ⟨hmem, hnmem, hreg, hqdom, hqnormal, ?_⟩
    rintro rfl
    let e := (isEmptyEquiv (Fin 0) A).toRingEquiv
    refine ⟨Ideal.quotientEquiv _ _ e ?_⟩
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(p : A)} = Ideal.span {constantCoeff Θ}
    rw [hΘ]

end MvPowerSeries
