/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Normal.Basic

/-! # The finite canonical Kummer character
Source: Stacks Project, Tag 0BUB, root-extension paragraph, and Tag 09I6.
-/

@[expose] public section
set_option autoImplicit false
universe u v w z
namespace IsDiscreteValuationRing

private theorem units_pow_surjective
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    (n : ℕ) (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    ∃ b : Rˣ, b ^ n = u := by
  let k := IsLocalRing.ResidueField R
  have hnk : (n : k) ≠ 0 := by
    simpa using (hnR.map (IsLocalRing.residue R)).ne_zero
  let : NeZero (n : k) := ⟨hnk⟩
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_pow_nat_eq (k := k)
    (IsLocalRing.residue R (u : R)) n
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    have : IsLocalRing.residue R (u : R) = 0 := by
      rw [← ha₀, h, zero_pow hn.ne']
    exact (u.isUnit.map (IsLocalRing.residue R)).ne_zero this
  let f : Polynomial R := Polynomial.X ^ n - Polynomial.C (u : R)
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  have hroot : Polynomial.aeval a₀ f = 0 := by
    simp only [f, Polynomial.aeval_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [ha₀]
    change IsLocalRing.residue R (u : R) - IsLocalRing.residue R (u : R) = 0
    exact sub_self _
  have hderiv : Polynomial.aeval a₀ f.derivative ≠ 0 := by
    simpa [f, Polynomial.derivative_X_pow] using
      mul_ne_zero hnk (pow_ne_zero (n - 1) ha₀ne)
  have hensel := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha, hres⟩ := hensel f hf a₀ hroot hderiv
  have hau : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).mp (hres ▸ ha₀ne)
  refine ⟨hau.unit, Units.ext ?_⟩
  simpa [f, Polynomial.IsRoot, sub_eq_zero] using ha

private theorem roots_fixed
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (E : Type w) [Field E] [Algebra K E]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R))
    (x : E) (hx : x ^ n = 1) (h : Gal(E/K)) : h x = x := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let g : R →+* E := (algebraMap K E).comp (algebraMap R K)
  have hg : Function.Injective g :=
    (algebraMap K E).injective.comp (IsFractionRing.injective R K)
  let f : rootsOfUnity n R →* rootsOfUnity n E := restrictRootsOfUnity g n
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply hg
    exact congrArg (fun z : rootsOfUnity n E ↦ ((z : Eˣ) : E)) hab
  have hcard := (AlgebraicGeometry.Scheme.strict_local_roots_of_unity R n ⟨hn, hu⟩).1
  have hsurj : Function.Surjective f := by
    apply ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, ?_⟩).2
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_injective f hfi
    · rw [hcard]
      exact card_rootsOfUnity E n
  obtain ⟨a, ha⟩ := hsurj (rootsOfUnity.mkOfPowEq x hx)
  have hxa : g ((a : Rˣ) : R) = x :=
    congrArg (fun z : rootsOfUnity n E ↦ ((z : Eˣ) : E)) ha
  rw [← hxa]
  exact h.commutes _

private theorem binomial_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) :
    Irreducible ((Polynomial.X : Polynomial K) ^ n -
      Polynomial.C (algebraMap R K π)) := by
  classical
  let f := (Polynomial.X : Polynomial R) ^ n - Polynomial.C π
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C π hn.ne'
  have hdeg : f.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hei : f.IsEisensteinAt (Ideal.span {π}) := by
    apply hf.isEisensteinAt_of_mem_of_notMem
    · rw [← hπ.maximalIdeal_eq]
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    · intro i hi
      rw [hdeg] at hi
      by_cases hi0 : i = 0
      · subst i
        simp [f, Ne.symm hn.ne', Polynomial.coeff_X_pow]
      · simp [f, Polynomial.coeff_X_pow, ne_of_lt hi, Polynomial.coeff_C, hi0]
    · simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Ne.symm hn.ne', if_false, Polynomial.coeff_C_zero, zero_sub,
        Ideal.neg_mem_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨b, hb⟩
      have hb' : 1 = π * b := mul_left_cancel₀ hπ.ne_zero (by
        calc π * 1 = π := mul_one π
             _ = π ^ 2 * b := hb
             _ = π * (π * b) := by ring)
      exact hπ.not_isUnit (isUnit_of_dvd_one ⟨b, hb'⟩)
  have hirr : Irreducible f := hei.irreducible
    (by rw [← hπ.maximalIdeal_eq]; infer_instance) hf.isPrimitive (hdeg ▸ hn)
  simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C] using hf.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hirr

private theorem fixed_of_pow_unit
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (E : Type w) [Field E] [Algebra K E]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R))
    (x : E) (u : Rˣ)
    (hx : x ^ n = algebraMap K E (algebraMap R K (u : R)))
    (h : Gal(E/K)) : h x = x := by
  obtain ⟨b, hb⟩ := units_pow_surjective R n hn hu u
  let g : R →+* E := (algebraMap K E).comp (algebraMap R K)
  have hbne : g (b : R) ≠ 0 := (b.isUnit.map g).ne_zero
  have hpow : (x / g (b : R)) ^ n = 1 := by
    rw [div_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hb, hx]
    exact div_self (u.isUnit.map g).ne_zero
  have hfix := roots_fixed R K E n hn hu _ hpow h
  have hgb : h (g (b : R)) = g (b : R) := h.commutes _
  rw [map_div₀, hgb] at hfix
  exact (div_left_inj' hbne).mp hfix

/-- The finite Kummer character for an invertible order, independent of the uniformizer.
Source: Stacks Project, pione.tex Tag 0BUB; fields.tex Tag 09I6.
(blueprint: lem-per-finite-canonical-kummer-character).

Proof: Hensel lifting gives nth roots of units. The n roots of unity in R exhaust all
roots in any extension, so Galois automorphisms fix them. Choose a root a of X^n-π in
Ksep. Eisenstein and Gauss show this binomial is irreducible over K. Its conjugates ζa
therefore realize all n values of h(a)/a, by normality of Ksep/K. This quotient is a
homomorphism because the roots of unity are fixed. Its kernel is the open stabilizer of a,
so the character is continuous. Changing the root or the uniformizer changes a by an nth
root of a unit, which is fixed by Hensel lifting. This proves the formula simultaneously
for every uniformizer and root, including n=1. -/
theorem finite_canonical_kummer_character
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R)) :
    ∃ χ : Gal(Ksep/K) →* rootsOfUnity n Ω,
      @Continuous _ _ inferInstance ⊥ (fun h ↦ (χ h : Ωˣ)) ∧
      Function.Surjective χ ∧
      ∀ (π : R), Irreducible π → ∀ a : Ksep,
        a ^ n = algebraMap K Ksep (algebraMap R K π) →
        ∀ h : Gal(Ksep/K), (((χ h : Ωˣ) : Ω)) = algebraMap Ksep Ω (h a / a) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let g : R →+* Ksep := (algebraMap K Ksep).comp (algebraMap R K)
  have hg : Function.Injective g :=
    (algebraMap K Ksep).injective.comp (IsFractionRing.injective R K)
  have hnE : (n : Ksep) ≠ 0 := by simpa using (hu.map g).ne_zero
  let : NeZero (n : Ksep) := ⟨hnE⟩
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq (g π) n
  have hane : a ≠ 0 := by
    intro hz
    have heq : g π = 0 := by rw [← ha, hz, zero_pow hn.ne']
    exact hπ.ne_zero (hg (heq.trans (map_zero g).symm))
  have hgπ : g π ≠ 0 := by simpa only [map_zero] using hg.ne hπ.ne_zero
  have hpow (h : Gal(Ksep/K)) : (h a / a) ^ n = 1 := by
    rw [div_pow, ← map_pow, ha]
    change h (algebraMap K Ksep (algebraMap R K π)) / g π = 1
    rw [h.commutes]
    exact div_self hgπ
  let χ : Gal(Ksep/K) →* rootsOfUnity n Ω := {
    toFun h := rootsOfUnity.mkOfPowEq (algebraMap Ksep Ω (h a / a)) (by
      rw [← map_pow, hpow, map_one])
    map_one' := by
      apply Subtype.ext
      apply Units.ext
      change algebraMap Ksep Ω ((1 : Gal(Ksep/K)) a / a) = 1
      simp [hane]
    map_mul' h k := by
      apply Subtype.ext
      apply Units.ext
      change algebraMap Ksep Ω ((h * k) a / a) =
        algebraMap Ksep Ω (h a / a) * algebraMap Ksep Ω (k a / a)
      rw [← map_mul]
      congr 1
      have heq := roots_fixed R K Ksep n hn hu (k a / a) (hpow k) h
      rw [map_div₀] at heq
      change h (k a) / a = _
      calc
        h (k a) / a = (h (k a) / h a) * (h a / a) := by
          field_simp [hane, (map_ne_zero h).2 hane]
        _ = _ := by rw [heq, mul_comm] }
  have hformula (π' : R) (hπ' : Irreducible π') (b : Ksep)
      (hb : b ^ n = algebraMap K Ksep (algebraMap R K π')) (h : Gal(Ksep/K)) :
      (((χ h : Ωˣ) : Ω)) = algebraMap Ksep Ω (h b / b) := by
    change b ^ n = g π' at hb
    obtain ⟨u, huπ⟩ := associated_of_irreducible R hπ hπ'
    have hbne : b ≠ 0 := by
      intro hz
      have heq : g π' = 0 := by rw [← hb, hz, zero_pow hn.ne']
      exact hπ'.ne_zero (hg (heq.trans (map_zero g).symm))
    have hunitpow : (b / a) ^ n = g (u : R) := by
      rw [div_pow, hb, ha, ← huπ, map_mul]
      exact mul_div_cancel_left₀ _ hgπ
    have heq := fixed_of_pow_unit R K Ksep n hn hu (b / a) u hunitpow h
    rw [map_div₀] at heq
    change algebraMap Ksep Ω (h a / a) = algebraMap Ksep Ω (h b / b)
    congr 1
    field_simp [hane, hbne, (map_ne_zero h).2 hane] at heq ⊢
    linear_combination -heq
  have hs : Function.Surjective χ := by
    intro z
    have hcard := (AlgebraicGeometry.Scheme.strict_local_roots_of_unity R n ⟨hn, hu⟩).1
    let gΩ : R →+* Ω := (algebraMap Ksep Ω).comp g
    let f : rootsOfUnity n R →* rootsOfUnity n Ω := restrictRootsOfUnity gΩ n
    have hfi : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Units.ext
      apply ((algebraMap Ksep Ω).injective.comp hg)
      exact congrArg (fun z : rootsOfUnity n Ω ↦ ((z : Ωˣ) : Ω)) hxy
    have hfs : Function.Surjective f := by
      apply ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, ?_⟩).2
      exact Nat.le_antisymm (Nat.card_le_card_of_injective f hfi)
        (hcard.symm ▸ card_rootsOfUnity Ω n)
    obtain ⟨ζ, hζ⟩ := hfs z
    have hζpow : (g ((ζ : Rˣ) : R)) ^ n = 1 := by
      rw [← map_pow, (mem_rootsOfUnity' n (ζ : Rˣ)).mp ζ.2, map_one]
    have hp := binomial_irreducible R K π hπ n hn
    have hmin : minpoly K a = Polynomial.X ^ n - Polynomial.C (algebraMap R K π) := by
      symm
      apply minpoly.eq_of_irreducible_of_monic hp
      · simpa [Polynomial.aeval_def, sub_eq_zero, g] using ha
      · exact Polynomial.monic_X_pow_sub_C _ hn.ne'
    obtain ⟨h, hh⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic (R := K) a) (x := g ((ζ : Rˣ) : R) * a) (by
        rw [hmin, Polynomial.aeval_def]
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, mul_pow]
        rw [hζpow, one_mul, ha]
        exact sub_self _)
    refine ⟨h, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change algebraMap Ksep Ω (h a / a) = ((z : Ωˣ) : Ω)
    rw [hh, mul_div_cancel_right₀ _ hane]
    exact congrArg (fun z : rootsOfUnity n Ω ↦ ((z : Ωˣ) : Ω)) hζ
  have hc : @Continuous _ _ inferInstance ⊥ (fun h ↦ (χ h : Ωˣ)) := by
    let : TopologicalSpace Ωˣ := ⊥
    let : DiscreteTopology Ωˣ := ⟨rfl⟩
    let f : Gal(Ksep/K) →* Ωˣ := (rootsOfUnity n Ω).subtype.comp χ
    apply continuous_of_continuousAt_one f
    change Filter.Tendsto f _ _
    rw [show nhds (f 1) = pure (1 : Ωˣ) by rw [map_one, nhds_discrete]]
    apply Filter.tendsto_pure.mpr
    apply Filter.mem_of_superset
      ((stabilizer_isOpen_of_isIntegral (K := K) a).mem_nhds (by simp))
    intro h hh
    apply Units.ext
    change algebraMap Ksep Ω (h a / a) = 1
    rw [show h a = a from hh, div_self hane, map_one]
  exact ⟨χ, hc, hs, hformula⟩

end IsDiscreteValuationRing
