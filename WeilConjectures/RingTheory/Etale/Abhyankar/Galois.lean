/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.Abhyankar.Tame
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Abhyankar's lemma for Galois field extensions

Let `O` be a discrete valuation ring with fraction field `F` and uniformizer `π`, and `K/F` a
finite Galois extension whose degree divides an integer `n` invertible in `O`. Then the integral
closure of `O₂ = O[t]/(tⁿ - π)` in `O₂ ⊗[O] K` is finite étale over `O₂`
(`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot_of_isGalois`).

By the fundamental identity `g e f = [K : F]`, the common ramification index `e` of the primes
of the integral closure `B` of `O` in `K` divides `n`, and the residue degrees are invertible in
the residue field, so that the residue field extensions are separable. As `B` is a semilocal
Dedekind domain, it is a principal ideal domain, and the product `ϖ` of its maximal ideals
satisfies `π = u ϖᵉ` with `u` a unit and `B ⧸ ϖ` a product of separable extensions of the residue
field of `O`. We conclude by the tame local computation
`IsDiscreteValuationRing.Abhyankar.etale_integralClosure_of_eq_unit_mul_pow`.
-/

@[expose] public section

open Polynomial TensorProduct Function

/-- A finite field extension whose degree is invertible in the base field is separable. -/
theorem Algebra.IsSeparable.of_natCast_finrank_ne_zero {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) :
    Algebra.IsSeparable F E := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  obtain ⟨k, hk⟩ := finInsepDegree_eq_pow F E q
  rw [isSeparable_iff_finInsepDegree_eq_one, hk]
  rw [← Field.finSepDegree_mul_finInsepDegree, hk, Nat.cast_mul, Nat.cast_pow] at h
  rcases hq with _ | ⟨hp, _⟩
  · exact one_pow k
  · rcases k with _ | k
    · rfl
    · simp [CharP.cast_eq_zero] at h

namespace IsDiscreteValuationRing

variable {O F K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field K] [Algebra F K] [Algebra O K] [IsScalarTower O F K]
  [FiniteDimensional F K]

/-- **Abhyankar's lemma for Galois field extensions.** See the module docstring. -/
theorem etale_integralClosure_adjoinRoot_of_isGalois [IsGalois F K] {n : ℕ}
    (hKn : Module.finrank F K ∣ n) (hn : IsUnit (n : O)) {π : O} (hπ : Irreducible π)
    (O₂ : Type*) [CommRing O₂] [Algebra O O₂] (hO₂ : IsAdjoinRoot O₂ (X ^ n - C π)) :
    Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] K)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] K)) := by
  let B := integralClosure O K
  have : IsDedekindDomain B := integralClosure.isDedekindDomain O F K
  have : Module.Finite O B := IsIntegralClosure.finite O F K B
  have : IsFractionRing B K := integralClosure.isFractionRing_of_finite_extension F K
  have hOK : Function.Injective (algebraMap O K) := by
    rw [IsScalarTower.algebraMap_eq O F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective O F)
  have : Module.IsTorsionFree O B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    fun x y h ↦ hOK (by rw [IsScalarTower.algebraMap_apply O B K, h,
      ← IsScalarTower.algebraMap_apply])
  have : IsGaloisGroup Gal(K/F) O B := IsGaloisGroup.of_isFractionRing Gal(K/F) O B F K
  let p := IsLocalRing.maximalIdeal O
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hpπ : p = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  -- the fundamental identity: `e ∣ n` and `f ∣ n`
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(K/F)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  set e := p.ramificationIdxIn B
  set f := p.inertiaDegIn B
  have hfn : f ∣ n := Dvd.dvd.trans ⟨(p.primesOver B).ncard * e, by rw [← hfund]; ring⟩ hKn
  obtain ⟨m, rfl⟩ : e ∣ n := Dvd.dvd.trans ⟨(p.primesOver B).ncard * f, by rw [← hfund]; ring⟩ hKn
  have he : IsUnit (e : O) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (dvd_mul_right e m)) hn
  have hm : m ≠ 0 := by
    rintro rfl
    rw [mul_zero, Nat.cast_zero] at hn
    exact not_isUnit_zero hn
  -- `B` is a principal ideal domain
  have hmax (P : Ideal B) (hP : P.IsMaximal) : P ∈ p.primesOver B :=
    ⟨hP.isPrime, ⟨(IsLocalRing.eq_maximalIdeal (hP.under O)).symm⟩⟩
  have : IsPrincipalIdealRing B :=
    .of_finite_maximals ((IsDedekindDomain.primesOver_finite p B).subset hmax)
  -- the ideal `J` of `B`, product of the maximal ideals, satisfies `𝔪_O B = Jᵉ`
  let s := (p.primesOver B).toFinset
  let J := ∏ P ∈ s, P
  have hmapJ : p.map (algebraMap O B) = J ^ e := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow (R := B) hp0, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun P hP ↦ ?_
    rw [Set.mem_toFinset] at hP
    have := hP.1
    have := hP.2
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(K/F)]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal J).principal
  rw [Ideal.submodule_span_eq] at hϖ
  have hassoc : Associated (algebraMap O B π) (ϖ ^ e) := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow, ← hϖ, ← hmapJ,
      hpπ, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨v, hv⟩ := hassoc
  have hπu : algebraMap O B π = ↑v⁻¹ * ϖ ^ e := by
    rw [← hv, mul_comm (algebraMap O B π), Units.inv_mul_cancel_left]
  -- `B ⧸ ϖ` is formally unramified over `O`
  have hsmax (P : Ideal B) (hP : P ∈ s) : P.IsMaximal := by
    rw [Set.mem_toFinset] at hP
    have := hP.1
    have := hP.2
    exact Ideal.IsMaximal.of_liesOver_isMaximal P p
  have hFU (P : Ideal B) (hP : P ∈ s) : Algebra.FormallyUnramified O (B ⧸ P) := by
    have := hsmax P hP
    rw [Set.mem_toFinset] at hP
    have := hP.2
    let _ : Field (O ⧸ p) := Ideal.Quotient.field p
    let _ : Field (B ⧸ P) := Ideal.Quotient.field P
    have : Module.Finite (O ⧸ p) (B ⧸ P) := Module.Finite.of_restrictScalars_finite O _ _
    have : Algebra.IsSeparable (O ⧸ p) (B ⧸ P) := by
      refine Algebra.IsSeparable.of_natCast_finrank_ne_zero fun h0 ↦ ?_
      rw [← Ideal.inertiaDeg_eq_of_isMaximal p P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(K/F)] at h0
      have hu := hn.map (Ideal.Quotient.mk p)
      obtain ⟨c, hc⟩ := hfn
      rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
      exact not_isUnit_zero hu
    have : Algebra.FormallyUnramified (O ⧸ p) (B ⧸ P) := .of_isSeparable _ _
    exact .comp O (O ⧸ p) (B ⧸ P)
  have : Algebra.FormallyUnramified O (B ⧸ Ideal.span {ϖ}) := by
    have hcop : (s : Set (Ideal B)).Pairwise (IsCoprime on fun P ↦ P) := fun P hP Q hQ hPQ ↦
      have := hsmax P hP
      have := hsmax Q hQ
      Ideal.isCoprime_of_isMaximal hPQ
    have hJ : J = ⨅ i : s, (i : Ideal B) :=
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop).trans iInf_subtype'
    have (i : s) : Algebra.FormallyUnramified O (B ⧸ (i : Ideal B)) := hFU i i.2
    let eCRT : (B ⧸ ⨅ i : s, (i : Ideal B)) ≃ₐ[O] Π i : s, B ⧸ (i : Ideal B) :=
      { Ideal.quotientInfRingEquivPiQuotient (fun i : s ↦ (i : Ideal B)) fun i j hij ↦
          hcop i.2 j.2 (Subtype.coe_injective.ne hij) with commutes' _ := rfl }
    rw [← hϖ, hJ]
    exact .of_equiv eCRT.symm
  -- the fraction field `K` of `B`
  have hπK : IsUnit (algebraMap O K π) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hOK).mpr hπ.ne_zero)
  have hspan (k : K) : ∃ j : ℕ, π ^ j • k ∈ Set.range (algebraMap B K) := by
    obtain ⟨y, hy0, hy⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff O F K).mpr (Algebra.IsAlgebraic.isAlgebraic k))
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
    have hk := hy.smul (↑w⁻¹ : O)
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at hk
    exact ⟨j, ⟨π ^ j • k, hk⟩, rfl⟩
  exact Abhyankar.etale_integralClosure_of_eq_unit_mul_pow Subtype.val_injective hπ hπK hspan he
    hm v⁻¹.isUnit hπu O₂ hO₂

end IsDiscreteValuationRing
