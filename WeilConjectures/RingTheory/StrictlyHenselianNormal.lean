/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Normal local domains with separably closed fraction field are strictly henselian

Let `A` be an integrally closed local domain whose fraction field `Ω` is separably closed (for
instance the localization at a maximal ideal of the integral closure of a domain in a separable
closure of its fraction field). Then `A` is strictly henselian
(`IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed`).

By Gauss's lemma a monic polynomial `f` over `A` factors over `A` as it factors over `Ω`. An
irreducible factor of `f` over `Ω` whose reduction has nonzero derivative is separable, hence
linear as `Ω` is separably closed. A simple root of the reduction of `f` is a root of the
reduction of exactly one factor, still simple, so it lifts by induction on the degree; and a
separable monic polynomial over the residue field lifts to a monic polynomial over `A` having a
linear factor.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace IsStrictlyHenselianLocalRing

variable {A Ω : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [Field Ω]
  [IsSepClosed Ω] [Algebra A Ω] [IsFractionRing A Ω]

omit [IsDomain A] [IsIntegrallyClosed A] in
include Ω in
/-- A monic polynomial over `A` which is irreducible over the separably closed fraction field and
whose reduction has nonzero derivative is linear. -/
lemma natDegree_eq_one_of_irreducible_map {f : A[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (algebraMap A Ω)))
    (hder : (f.map (residue A)).derivative ≠ 0) : f.natDegree = 1 := by
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hder' : (f.map (algebraMap A Ω)).derivative ≠ 0 := by
    rw [derivative_map]
    intro h
    apply hder
    rw [derivative_map, (Polynomial.map_eq_zero_iff hinj).1 h, Polynomial.map_zero]
  have hsep : (f.map (algebraMap A Ω)).Separable := (separable_iff_derivative_ne_zero hirr).2 hder'
  have h1 := IsSepClosed.degree_eq_one_of_irreducible Ω hirr hsep
  rw [degree_map_eq_of_injective hinj, degree_eq_natDegree hf.ne_zero] at h1
  exact_mod_cast h1

omit [IsDomain A] [IsLocalRing A] [IsSepClosed Ω] in
include Ω in
/-- A monic polynomial over `A` of positive degree which is not linear after an irreducible
factorization over `Ω` factors over `A`: either `f` is irreducible over `Ω`, or it is a product
of two monic polynomials over `A` of positive degree. -/
lemma irreducible_or_exists_mul {f : A[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap A Ω)) ∨ ∃ g h : A[X], g.Monic ∧ h.Monic ∧
      0 < g.natDegree ∧ 0 < h.natDegree ∧ f = g * h := by
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  set F := f.map (algebraMap A Ω)
  have hFm : F.Monic := hf.map _
  have hFdeg : F.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  by_cases hirr : Irreducible F
  · exact Or.inl hirr
  refine Or.inr ?_
  have hFu : ¬ IsUnit F := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hFm.ne_zero, hFdeg]
    exact_mod_cast hdeg.ne'
  obtain ⟨g₀, hg₀, hg₀F⟩ := WfDvdMonoid.exists_irreducible_factor hFu hFm.ne_zero
  have hg₀0 : g₀ ≠ 0 := hg₀.ne_zero
  set g₁ := g₀ * C g₀.leadingCoeff⁻¹
  have hg₁m : g₁.Monic := monic_mul_leadingCoeff_inv hg₀0
  have hg₁F : g₁ ∣ F := by
    obtain ⟨q, hq⟩ := hg₀F
    exact ⟨C g₀.leadingCoeff * q, by
      rw [hq, mul_assoc, ← mul_assoc (C _), ← C_mul,
        inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hg₀0), C_1, one_mul]⟩
  obtain ⟨q₁, hq₁⟩ := hg₁F
  have hq₁m : q₁.Monic := by
    have := hFm
    rw [hq₁] at this
    exact hg₁m.of_mul_monic_left this
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hf ⟨q₁, hq₁⟩
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hf ⟨g₁, by rw [mul_comm]; exact hq₁⟩
  rw [hg₁m.leadingCoeff, C_1, mul_one] at hg
  rw [hq₁m.leadingCoeff, C_1, mul_one] at hh
  have hgm : g.Monic := by
    apply Polynomial.Monic.def.2
    rw [← (map_eq_one_iff (algebraMap A Ω) hinj), ← leadingCoeff_map_of_injective hinj, hg]
    exact hg₁m
  have hhm : h.Monic := by
    apply Polynomial.Monic.def.2
    rw [← (map_eq_one_iff (algebraMap A Ω) hinj), ← leadingCoeff_map_of_injective hinj, hh]
    exact hq₁m
  have hfgh : f = g * h := by
    apply map_injective _ hinj
    rw [Polynomial.map_mul, hg, hh]
    exact hq₁
  have hg₁deg : 0 < g₁.natDegree := by
    rw [natDegree_mul hg₀0 (by simpa using hg₀0), natDegree_C, add_zero]
    exact natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hg₀)
  have hq₁deg : 0 < q₁.natDegree := by
    by_contra h0
    have hq1 : q₁ = 1 := (Polynomial.Monic.natDegree_eq_zero hq₁m).1 (by omega)
    apply hirr
    rw [hq₁, hq1, mul_one]
    refine (irreducible_mul_isUnit ?_).2 hg₀
    exact isUnit_C.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hg₀0)).isUnit
  refine ⟨g, h, hgm, hhm, ?_, ?_, hfgh⟩
  · rwa [← natDegree_map_eq_of_injective hinj g, hg]
  · rwa [← natDegree_map_eq_of_injective hinj h, hh]

omit [IsLocalRing A] [IsSepClosed Ω] in
include Ω in
/-- A monic polynomial of positive degree over `A` has a monic factor over `A` of positive degree
which is irreducible over `Ω`. -/
lemma exists_dvd_irreducible_map (f : A[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ g : A[X], g.Monic ∧ 0 < g.natDegree ∧ Irreducible (g.map (algebraMap A Ω)) ∧ g ∣ f := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    rcases irreducible_or_exists_mul (Ω := Ω) hf hdeg with hirr | ⟨g, h, hg, hh, hg0, hh0, rfl⟩
    · exact ⟨f, hf, hdeg, hirr, dvd_rfl⟩
    · have hgh := natDegree_mul hg.ne_zero hh.ne_zero
      obtain ⟨g', hg', hg'0, hirr, hdvd⟩ := ih g.natDegree (by omega) g hg hg0 rfl
      exact ⟨g', hg', hg'0, hirr, hdvd.trans (dvd_mul_right g h)⟩

omit [IsDomain A] [IsIntegrallyClosed A] in
lemma aeval_residue_eq_eval_map (f : A[X]) (a : ResidueField A) :
    aeval a f = (f.map (residue A)).eval a := by
  rw [aeval_def, eval_map, ResidueField.algebraMap_eq]

include Ω in
/-- **Simple roots lift**: a simple root in the residue field of a monic polynomial over `A`
lifts to a root in `A`. -/
lemma exists_isRoot_residue_eq (f : A[X]) (hf : f.Monic) (a₀ : ResidueField A)
    (h₁ : aeval a₀ f = 0) (h₂ : aeval a₀ (derivative f) ≠ 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    have hdeg : 0 < f.natDegree := by
      by_contra h0
      rw [(Polynomial.Monic.natDegree_eq_zero hf).1 (by omega), map_one] at h₁
      exact one_ne_zero h₁
    rcases irreducible_or_exists_mul (Ω := Ω) hf hdeg with hirr | ⟨g, h, hg, hh, hg0, hh0, rfl⟩
    · have hder : (f.map (residue A)).derivative ≠ 0 := by
        intro h0
        apply h₂
        rw [aeval_residue_eq_eval_map, ← derivative_map, h0, eval_zero]
      have h1 := natDegree_eq_one_of_irreducible_map (Ω := Ω) hf hirr hder
      set c := f.coeff 0
      have hfX : f = X + C c := hf.eq_X_add_C h1
      refine ⟨-c, ?_, ?_⟩
      · rw [hfX, IsRoot.def, eval_add, eval_X, eval_C, neg_add_cancel]
      · rw [hfX, map_add, aeval_X, aeval_C, ResidueField.algebraMap_eq] at h₁
        rw [map_neg, neg_eq_iff_add_eq_zero, add_comm, h₁]
    · have hgh := natDegree_mul hg.ne_zero hh.ne_zero
      rw [map_mul, mul_eq_zero] at h₁
      rw [derivative_mul, map_add, map_mul, map_mul] at h₂
      rcases h₁ with h₁ | h₁
      · rw [h₁, zero_mul, add_zero] at h₂
        obtain ⟨a, ha, rfl⟩ := ih g.natDegree (by omega) g hg h₁ (left_ne_zero_of_mul h₂) rfl
        exact ⟨a, by rw [IsRoot.def, eval_mul, ha.eq_zero, zero_mul], rfl⟩
      · rw [h₁, mul_zero, zero_add] at h₂
        obtain ⟨a, ha, rfl⟩ := ih h.natDegree (by omega) h hh h₁ (right_ne_zero_of_mul h₂) rfl
        exact ⟨a, by rw [IsRoot.def, eval_mul, ha.eq_zero, mul_zero], rfl⟩

include Ω in
lemma henselianLocalRing : HenselianLocalRing A :=
  ((HenselianLocalRing.TFAE A).out 1 0).mp fun f hf a₀ h₁ h₂ ↦
    exists_isRoot_residue_eq (Ω := Ω) f hf a₀ h₁ h₂

include Ω in
lemma isSepClosed_residueField_of_isFractionRing : IsSepClosed (ResidueField A) := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep ↦ ?_
  obtain ⟨f, hfp, hdeg, hf⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective _ residue_surjective p) hm
  have hfdeg : 0 < f.natDegree := by
    rw [hdeg]
    exact natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  obtain ⟨g, hg, hg0, hgirr, hgf⟩ := exists_dvd_irreducible_map (Ω := Ω) f hf hfdeg
  have hgsep : (g.map (residue A)).Separable :=
    hsep.of_dvd (hfp ▸ Polynomial.map_dvd (residue A) hgf)
  have hder : (g.map (residue A)).derivative ≠ 0 := by
    intro h0
    have hu : IsUnit (g.map (residue A)) := isCoprime_zero_right.1 (h0 ▸ hgsep)
    have := natDegree_eq_zero_of_isUnit hu
    rw [hg.natDegree_map] at this
    omega
  have h1 := natDegree_eq_one_of_irreducible_map (Ω := Ω) hg hgirr hder
  set c := g.coeff 0
  have hgX : g = X + C c := hg.eq_X_add_C h1
  refine ⟨residue A (-c), eval_eq_zero_of_dvd_of_eval_eq_zero
    (hfp ▸ Polynomial.map_dvd (residue A) hgf) ?_⟩
  rw [hgX, Polynomial.map_add, map_X, map_C, eval_add, eval_X, eval_C, map_neg, neg_add_cancel]

variable (Ω) in
include Ω in
/-- An integrally closed local domain whose fraction field is separably closed is strictly
henselian. -/
theorem of_isFractionRing_of_isSepClosed : IsStrictlyHenselianLocalRing A :=
  have := henselianLocalRing (A := A) (Ω := Ω)
  ⟨isSepClosed_residueField_of_isFractionRing (Ω := Ω)⟩

end IsStrictlyHenselianLocalRing

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

/-- The localization at a prime `Q` of the integral closure of `R` in a field `Ω` maps to `Ω`. -/
noncomputable def atPrimeToField : Localization.AtPrime Q →+* Ω :=
  IsLocalization.lift (M := Q.primeCompl) (g := (integralClosure R Ω).val.toRingHom) fun s ↦
    IsUnit.mk0 _ fun h ↦ s.2 (by
      have : s.1 = 0 := Subtype.ext h
      rw [this]
      exact Q.zero_mem)

@[simp]
lemma atPrimeToField_algebraMap (b : integralClosure R Ω) :
    atPrimeToField Q (algebraMap _ (Localization.AtPrime Q) b) = b :=
  IsLocalization.lift_eq _ _

lemma injective_atPrimeToField : Function.Injective (atPrimeToField Q) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
  rw [atPrimeToField, IsLocalization.lift_mk'_spec, mul_zero] at hx
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨1, by rw [OneMemClass.coe_one, one_mul]; exact Subtype.ext hx⟩

variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]

/-- The localization at a prime of the integral closure of a domain `R` in a separably closed
field `Ω` algebraic over `R` is strictly henselian. -/
theorem isStrictlyHenselianLocalRing_atPrime (hR : Function.Injective (algebraMap R Ω)) :
    IsStrictlyHenselianLocalRing (Localization.AtPrime Q) := by
  have : IsFractionRing (integralClosure R Ω) Ω := integralClosure.isFractionRing_of_algebraic
    fun x hx ↦ hR (hx.trans (map_zero _).symm)
  have : IsIntegrallyClosed (integralClosure R Ω) :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff Ω).mp integralClosure_idem
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization _ Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime Q) Ω := (atPrimeToField Q).toAlgebra
  have : IsScalarTower (integralClosure R Ω) (Localization.AtPrime Q) Ω :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (atPrimeToField_algebraMap Q b).symm
  have : IsFractionRing (Localization.AtPrime Q) Ω :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl _ Ω
  exact IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed Ω

end Ideal
