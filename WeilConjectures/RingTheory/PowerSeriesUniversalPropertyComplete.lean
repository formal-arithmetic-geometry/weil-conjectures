/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Universal property of power series over an adically complete ring

If `T` is `a`-adically complete, then a ring map `α : Λ → T` and elements `t₁, …, tₙ` of `a`
extend uniquely to a ring map `Λ⟦X₁, …, Xₙ⟧ → T` sending `Xᵢ` to `tᵢ`.

## Implementation details

`F.truncTotal m` retains exactly the coefficients of total degree less than `m`, so
`MvPolynomial.eval₂ α t (F.truncTotal m)` is the finite sum of `α(a_E) * t^E` over `|E| < m`.
No continuity hypothesis is needed for uniqueness.

## References

* Stacks Project, proofs of Tags 07NL, 07NN and 032A
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- Universal property of power series over an `a`-adically complete ring `T`: given
`α : Λ →+* T` and `t i ∈ a`, there is a unique ring map `Φ` extending `α` with `Φ (X i) = t i`.
Moreover `Φ F` is the unique element congruent modulo every `a ^ m` to the evaluation of the
truncation of `F` below total degree `m`. -/
theorem exists_ringHom_of_isAdicComplete
    {Λ : Type u} {T : Type v} [CommRing Λ] [CommRing T]
    (a : Ideal T) [IsAdicComplete a T] (α : Λ →+* T)
    (n : ℕ) (t : Fin n → T) (ht : ∀ i : Fin n, t i ∈ a) :
    ∃ Φ : MvPowerSeries (Fin n) Λ →+* T,
      (∀ r : Λ, Φ (C r) = α r) ∧
      (∀ i : Fin n, Φ (X i) = t i) ∧
      (∀ (F : MvPowerSeries (Fin n) Λ) (y : T),
        (∀ m : ℕ, 1 ≤ m →
          Ideal.Quotient.mk (a ^ m) y =
            Ideal.Quotient.mk (a ^ m) (MvPolynomial.eval₂ α t (F.truncTotal m))) ↔
        y = Φ F) ∧
      (∀ Ψ : MvPowerSeries (Fin n) Λ →+* T,
        (∀ r : Λ, Ψ (C r) = α r) →
        (∀ i : Fin n, Ψ (X i) = t i) → Ψ = Φ) := by
  classical
  have eval_mem_pow (m : ℕ) {p : MvPolynomial (Fin n) Λ}
      (hp : p ∈ MvPolynomial.idealOfVars (Fin n) Λ ^ m) :
      MvPolynomial.eval₂ α t p ∈ a ^ m := by
    have h : MvPolynomial.idealOfVars (Fin n) Λ ≤
        a.comap (MvPolynomial.eval₂Hom α t) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simpa using ht i
    exact ((pow_le_pow_left' h m).trans
      (Ideal.le_comap_pow (MvPolynomial.eval₂Hom α t) m)) hp
  let q (m : ℕ) : MvPowerSeries (Fin n) Λ →+* T ⧸ a ^ m :=
    (Ideal.quotientMap (a ^ m) (MvPolynomial.eval₂Hom α t)
      (fun _ hp ↦ eval_mem_pow m hp)).comp
        (truncTotalAlgHom (Fin n) Λ m).toRingHom
  have hq (F : MvPowerSeries (Fin n) Λ) (m : ℕ) : q m F =
      Ideal.Quotient.mk (a ^ m) (MvPolynomial.eval₂ α t (truncTotal m F)) := by
    dsimp [q, truncTotalAlgHom]
    exact Ideal.quotientMap_mk
  have hcompat : ∀ {k m : ℕ} (h : k ≤ m),
      (Ideal.Quotient.factorPow a h).comp (q m) = q k := by
    intro k m h
    ext F
    simp only [RingHom.comp_apply, hq, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← MvPolynomial.eval₂_sub]
    exact eval_mem_pow k (truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl F)
  let Φ := IsAdicComplete.liftRingHom a q hcompat
  have hΦ (F : MvPowerSeries (Fin n) Λ) (m : ℕ) :
      Ideal.Quotient.mk (a ^ m) (Φ F) =
        Ideal.Quotient.mk (a ^ m) (MvPolynomial.eval₂ α t (truncTotal m F)) := by
    rw [IsAdicComplete.mk_liftRingHom, hq]
  have sep {x y : T}
      (h : ∀ m : ℕ, Ideal.Quotient.mk (a ^ m) x = Ideal.Quotient.mk (a ^ m) y) :
      x = y := by
    have heq := IsHausdorff.funext' a (f := fun _ : Unit ↦ x)
      (g := fun _ : Unit ↦ y) (fun m _ ↦ h m)
    exact congrFun heq ()
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro r
    apply sep
    intro m
    rw [hΦ]
    by_cases hm : m = 0
    · subst m
      simp [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    · have hC : truncTotal m (C r : MvPowerSeries (Fin n) Λ) =
          MvPolynomial.C r := by
        ext d
        by_cases hd : d = 0
        · subst d
          simp [coeff_truncTotal_eq_ite, Nat.pos_of_ne_zero hm]
        · simp [coeff_truncTotal_eq_ite, coeff_C, MvPolynomial.coeff_C, hd, Ne.symm hd]
      simp [hC]
  · intro i
    apply sep
    intro m
    rw [hΦ]
    have hX : truncTotal m (X i : MvPowerSeries (Fin n) Λ) =
        if 1 < m then MvPolynomial.X i else 0 := by
      by_cases hm : 1 < m <;> simp only [hm, ite_true, ite_false]
      · ext d
        by_cases hd : d = Finsupp.single i 1
        · subst d
          simp [coeff_truncTotal_eq_ite, hm, MvPolynomial.coeff_X]
        · simp [coeff_truncTotal_eq_ite, coeff_X, MvPolynomial.coeff_X, hd, Ne.symm hd]
      · ext d
        by_cases hd : d = Finsupp.single i 1
        · subst d
          simp [coeff_truncTotal_eq_ite, hm]
        · simp [coeff_truncTotal_eq_ite, coeff_X, hd]
    rw [hX]
    split_ifs with hm
    · simp only [MvPolynomial.eval₂_X]
    · simp only [map_zero, MvPolynomial.eval₂_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (Ideal.pow_le_pow_right (Nat.le_of_not_gt hm)) (by simpa using ht i)
  · intro F y
    constructor
    · intro hy
      apply sep
      intro m
      by_cases hm : m = 0
      · subst m
        simp [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      · exact (hy m (Nat.one_le_iff_ne_zero.mpr hm)).trans (hΦ F m).symm
    · rintro rfl m _
      exact hΦ F m
  · intro Ψ hC hX
    apply DFunLike.coe_injective
    apply IsHausdorff.funext' a
    intro m F
    rw [hΦ]
    have hpoly : ∀ p : MvPolynomial (Fin n) Λ,
        Ψ (p : MvPowerSeries (Fin n) Λ) = MvPolynomial.eval₂ α t p := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r => simpa using hC r
      | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
      | mul_X p i hp => simp [hp, hX]
    have htail : F - (truncTotal m F : MvPolynomial (Fin n) Λ) ∈
        (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) Λ))) ^ m := by
      have h := (power_series_mem_combined_ideal_pow_iff Λ (⊥ : Ideal Λ) n m
        (F - (truncTotal m F : MvPolynomial (Fin n) Λ))).mpr ?_
      · simpa using h
      · intro E hE
        simp [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hE]
    have hvars : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) Λ)) ≤
        a.comap Ψ := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change Ψ (X i) ∈ a
      rw [hX]
      exact ht i
    have hmem := ((pow_le_pow_left' hvars m).trans (Ideal.le_comap_pow Ψ m)) htail
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    change Ψ (F - (truncTotal m F : MvPolynomial (Fin n) Λ)) ∈ a ^ m at hmem
    simpa only [map_sub, hpoly] using hmem

end MvPowerSeries
