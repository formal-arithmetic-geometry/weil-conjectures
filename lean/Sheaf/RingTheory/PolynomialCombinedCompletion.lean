/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.CompletionEquivPowerQuotients
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import Sheaf.RingTheory.PolynomialCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase

/-! # Completion of a polynomial ring at the combined ideal

Source: Stacks Project, Tags 054L and 0AGX, coefficient calculation in
lem-trf-smooth-rational-point-completion, Steps 6–7.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

private theorem completion_mem_map_pow_iff
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion I R) :
    x ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n ↔
      AdicCompletion.evalₐ I n x = 0 := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change AdicCompletion.eval I R n x = 0 ↔ AdicCompletion.evalₐ I n x = 0
  have hf := AdicCompletion.factor_eval_eq_evalₐ I x
    (show (I ^ n • ⊤ : Ideal R) ≤ I ^ n by simp [smul_eq_mul])
  have hi : Function.Injective
      (Submodule.factor (show (I ^ n • ⊤ : Ideal R) ≤ I ^ n by
        simp [smul_eq_mul])) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    simpa [smul_eq_mul] using Ideal.Quotient.eq.mp hab
  rw [← hf]
  exact (map_eq_zero_iff _ hi).symm

private theorem polynomial_to_series_power_membership
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (d n : ℕ)
    (p : MvPolynomial (Fin d) R) :
    let A := AdicCompletion I R
    let f := (coeToMvPowerSeries.algHom (R := R) A).toRingHom
    let Q := I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R
    let H := (I.map (algebraMap R A)).map (MvPowerSeries.C (σ := Fin d)) ⊔
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A)))
    f p ∈ H ^ n ↔ p ∈ Q ^ n := by
  classical
  dsimp only
  rw [MvPowerSeries.c_eq_algebraMap, power_series_mem_combined_ideal_pow_iff,
    mem_combined_ideal_pow_iff]
  constructor
  · intro hp E
    by_cases hE : E.degree < n
    · have hh := hp E hE
      rw [completion_mem_map_pow_iff I hI] at hh
      have hc : MvPowerSeries.coeff E
          ((coeToMvPowerSeries.algHom (R := R) (AdicCompletion I R)).toRingHom p) =
          algebraMap R (AdicCompletion I R) (p.coeff E) := by
        simp [coeToMvPowerSeries.algHom_apply, MvPowerSeries.coeff_map, coeff_coe]
      rw [hc] at hh
      change AdicCompletion.evalₐ I (n - E.degree) (AdicCompletion.of I R (p.coeff E)) = 0 at hh
      rw [AdicCompletion.evalₐ_of] at hh
      exact Ideal.Quotient.eq_zero_iff_mem.mp hh
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hE)]
  · intro hp E hE
    rw [completion_mem_map_pow_iff I hI]
    have hc : MvPowerSeries.coeff E
        ((coeToMvPowerSeries.algHom (R := R) (AdicCompletion I R)).toRingHom p) =
        algebraMap R (AdicCompletion I R) (p.coeff E) := by
      simp [coeToMvPowerSeries.algHom_apply, MvPowerSeries.coeff_map, coeff_coe]
    rw [hc]
    change AdicCompletion.evalₐ I (n - E.degree) (AdicCompletion.of I R (p.coeff E)) = 0
    rw [AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hp E)

private theorem polynomial_to_series_quotient_surjective
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (d n : ℕ)
    (F : MvPowerSeries (Fin d) (AdicCompletion I R)) :
    let A := AdicCompletion I R
    let f := (coeToMvPowerSeries.algHom (R := R) A).toRingHom
    let H := (I.map (algebraMap R A)).map (MvPowerSeries.C (σ := Fin d)) ⊔
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A)))
    ∃ p : MvPolynomial (Fin d) R, f p - F ∈ H ^ n := by
  classical
  let A := AdicCompletion I R
  let rho := ((AdicCompletion.evalₐ I n).toRingHom).comp (algebraMap R A)
  let t := MvPowerSeries.truncTotal n F
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective rho
    (by
      intro b
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨a, by simp [rho, A]⟩)
    (MvPolynomial.map (AdicCompletion.evalₐ I n).toRingHom t)
  refine ⟨p, ?_⟩
  apply (power_series_mem_combined_ideal_pow_iff A
    (I.map (algebraMap R A)) d n _).mpr
  intro E hE
  rw [map_sub, completion_mem_map_pow_iff I hI]
  have hcoeff := congrArg (MvPolynomial.coeff E) hp
  simp only [MvPolynomial.coeff_map] at hcoeff
  change AdicCompletion.evalₐ I n (algebraMap R A (p.coeff E)) =
    AdicCompletion.evalₐ I n (t.coeff E) at hcoeff
  rw [MvPowerSeries.coeff_truncTotal F hE] at hcoeff
  have hval : AdicCompletion.evalₐ I n
      (algebraMap R A (p.coeff E) - MvPowerSeries.coeff E F) = 0 := by
    rw [map_sub, hcoeff, sub_self]
  have hsmall := (completion_mem_map_pow_iff I hI (n - E.degree) _).mp
    (Ideal.pow_le_pow_right (Nat.sub_le n E.degree)
      ((completion_mem_map_pow_iff I hI n _).mpr hval))
  change AdicCompletion.evalₐ I (n - E.degree)
    (MvPowerSeries.coeff E
      (MvPowerSeries.map (algebraMap R A) (p : MvPowerSeries (Fin d) R)) -
      MvPowerSeries.coeff E F) = 0
  simpa only [MvPowerSeries.coeff_map, coeff_coe] using hsmall

/-- Complete polynomials at the ideal generated by the base maximal ideal and all
variables. Constants are compatible on every quotient, and the residue map is the
constant coefficient map.

Source: the coefficient calculation in Steps 6–7 of
lem-trf-smooth-rational-point-completion.
(blueprint: lem-trf-polynomial-combined-completion)

Proof: The coefficient criterion for `(m,X)^n` identifies the quotient with the
finite family of coefficients of exponents E of degree less than n, where the
coefficient at E is taken modulo m^(n-degree E). The transition maps reduce these
coefficients. Taking their inverse limit assigns to each exponent a compatible
m-adic coefficient, hence an element of the completed base. Addition and
multiplication agree coefficient by coefficient; the multiplication coefficient
is a finite convolution. The two coefficient constructions are inverse ring
maps. On a constant series the level n coordinate is the constant polynomial of
the corresponding base coordinate. At level one only exponent zero survives,
which gives the residue assertion. The empty variable set and n=0 are included. -/
theorem combinedIdeal_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (d : ℕ) :
    let I := IsLocalRing.maximalIdeal R
    let Q := I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R
    ∃ E : AdicCompletion Q (MvPolynomial (Fin d) R) ≃+*
        MvPowerSeries (Fin d) (AdicCompletion I R),
      (∀ (n : ℕ) (x : AdicCompletion I R) (a : R),
        AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
          AdicCompletion.evalₐ Q n (E.symm (MvPowerSeries.C x)) =
            Ideal.Quotient.mk (Q ^ n) (C a)) ∧
      (∀ (y : AdicCompletion Q (MvPolynomial (Fin d) R)) (p : MvPolynomial (Fin d) R),
        AdicCompletion.evalₐ Q 1 y = Ideal.Quotient.mk (Q ^ 1) p →
          AdicCompletion.evalOneₐ I (MvPowerSeries.constantCoeff (E y)) =
            IsLocalRing.residue R (constantCoeff p)) := by
  classical
  intro I Q
  let A := AdicCompletion I R
  let T := MvPowerSeries (Fin d) A
  let f : MvPolynomial (Fin d) R →+* T := (coeToMvPowerSeries.algHom (R := R) A).toRingHom
  let H : Ideal T := (I.map (algebraMap R A)).map MvPowerSeries.C ⊔
    Ideal.span (Set.range MvPowerSeries.X)
  have hI : I.FG := I.fg_of_isNoetherianRing
  let : IsNoetherianRing A := AdicCompletion.isNoetherianRing I
  let : IsAdicComplete (I.map (algebraMap R A)) A :=
    AdicCompletion.isAdicComplete_self I hI
  let : IsAdicComplete H T := power_series_complete_over_complete_base A
    (I.map (algebraMap R A)) d
  have hmem (n : ℕ) (p : MvPolynomial (Fin d) R) :
      f p ∈ H ^ n ↔ p ∈ Q ^ n := polynomial_to_series_power_membership I hI d n p
  have hle : Q ≤ H.comap f := by
    intro p hp
    simpa using (hmem 1 p).mpr (by simpa using hp)
  let q (n : ℕ) := Ideal.powerQuotientMap f Q H hle n
  have hq : ∀ n, Function.Bijective (q n) := by
    intro n
    constructor
    · intro x y hxy
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply Ideal.Quotient.eq.mpr
      apply (hmem n (p - r)).mp
      change Ideal.Quotient.mk (H ^ n) (f p) =
        Ideal.Quotient.mk (H ^ n) (f r) at hxy
      rw [map_sub]
      exact Ideal.Quotient.eq.mp hxy
    · intro x
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, hp⟩ := polynomial_to_series_quotient_surjective I hI d n F
      exact ⟨Ideal.Quotient.mk (Q ^ n) p, Ideal.Quotient.eq.mpr hp⟩
  obtain ⟨E₀, hE₀⟩ := AdicCompletion.equiv_of_powerQuotient_bijective f Q H hle hq
  let E := E₀.trans (AdicCompletion.ofAlgEquiv H).symm.toRingEquiv
  have hE (n : ℕ) (y : AdicCompletion Q (MvPolynomial (Fin d) R)) :
      Ideal.Quotient.mk (H ^ n) (E y) = q n (AdicCompletion.evalₐ Q n y) := by
    change Ideal.Quotient.mk (H ^ n) ((AdicCompletion.ofAlgEquiv H).symm (E₀ y)) = _
    rw [AdicCompletion.mk_ofAlgEquiv_symm, hE₀]
    rfl
  have hfC (a : R) : f (C a) = MvPowerSeries.C (algebraMap R A a) := by
    change MvPowerSeries.map (algebraMap R A)
      ((C a : MvPolynomial (Fin d) R) : MvPowerSeries (Fin d) R) = _
    rw [coe_C, MvPowerSeries.map_C]
  have hfcoeff (p : MvPolynomial (Fin d) R) :
      MvPowerSeries.constantCoeff (f p) = algebraMap R A (constantCoeff p) := by
    change MvPowerSeries.constantCoeff
      (MvPowerSeries.map (algebraMap R A) (p : MvPowerSeries (Fin d) R)) = _
    change MvPowerSeries.coeff 0
      (MvPowerSeries.map (algebraMap R A) (p : MvPowerSeries (Fin d) R)) = _
    rw [MvPowerSeries.coeff_map, coeff_coe, constantCoeff_eq]
  refine ⟨E, ?_, ?_⟩
  · intro n x a ha
    apply (hq n).injective
    rw [← hE, E.apply_symm_apply]
    change Ideal.Quotient.mk (H ^ n) (MvPowerSeries.C x) =
      Ideal.Quotient.mk (H ^ n) (f (C a))
    apply Ideal.Quotient.eq.mpr
    rw [hfC, ← map_sub]
    apply Ideal.pow_right_mono le_sup_left n
    rw [← Ideal.map_pow]
    apply Ideal.mem_map_of_mem
    apply (completion_mem_map_pow_iff I hI n _).mpr
    change AdicCompletion.evalₐ I n (x - AdicCompletion.of I R a) = 0
    rw [map_sub, ha, AdicCompletion.evalₐ_of, sub_self]
  · intro y p hp
    have he := hE 1 y
    rw [hp] at he
    have hm : E y - f p ∈ H ^ 1 := Ideal.Quotient.eq.mp he
    have hc := (power_series_mem_combined_ideal_pow_iff A
      (I.map (algebraMap R A)) d 1 _).mp hm 0 (by simp)
    have hz : AdicCompletion.evalₐ I 1
        (MvPowerSeries.constantCoeff (E y) - algebraMap R A (constantCoeff p)) = 0 := by
      apply (completion_mem_map_pow_iff I hI 1 _).mp
      simpa only [map_sub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        hfcoeff, map_zero, tsub_zero, pow_one] using hc
    have hz' := congrArg (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)) hz
    rw [AdicCompletion.factorₐ_evalₐ_one, map_zero, map_sub,
      AdicCompletion.algebraMap_apply, AdicCompletion.evalOneₐ_of] at hz'
    change AdicCompletion.evalOneₐ I (MvPowerSeries.constantCoeff (E y)) =
      Ideal.Quotient.mk I (constantCoeff p)
    simpa using sub_eq_zero.mp hz'


end MvPolynomial
