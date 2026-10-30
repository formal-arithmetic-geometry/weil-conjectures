/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral.ResiduePth

/-!
# Density of `F` in its decomposition field (rank one)

Let `Ω` be separably closed and separable over a subfield `F`, and `𝒪` a valuation subring of `Ω`
of rank one. Then every element of the decomposition field `Z` of `𝒪` over `F` (the fixed field
of the decomposition group) is a limit of elements of `F`
(`ValuationSubring.exists_valuation_sub_lt_of_mem_fixedField`). This is the classical fact that
the henselisation of a rank-one valued field lies in its completion.

The proof is elementary: for `a ∈ Z ∩ 𝒪` there is `e`, integral over `𝒪 ∩ F` and fixed by the
automorphisms fixing `a`, with `v e = 1` and `v (σ e) < 1` for every conjugate `σ a ≠ a`
(`exists_isIntegral_separating`). In rank one the conjugates of `e ^ N` other than those over
`a` become arbitrarily small, so traces of `a s e ^ N` and `s e ^ N` (`a = (a s) / s`) give
arbitrarily good approximations of `a` in `F` (`exists_mem_valuation_sub_lt_of_conj`).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- **Sum of conjugates, with precision.** Let `Ω` be separably closed and separable over `F`,
and `x ∈ Ω` such that every conjugate `σ x ≠ x` has `v (σ x) < γ`. Then the sum of the conjugates
of `x` is an element `c ∈ F` with `v (c - x) < γ`. -/
theorem exists_mem_valuation_sub_lt_of_conj [IsSepClosed Ω] {F : Subfield Ω}
    [Algebra.IsSeparable F Ω] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {γ : Γ} (hγ : γ ≠ 0) {x : Ω}
    (hconj : ∀ σ : Ω ≃ₐ[F] Ω, σ x ≠ x → v (σ x) < γ) :
    ∃ c ∈ F, v (c - x) < γ := by
  classical
  have := IsSepClosed.isGalois_of_isSeparable (F := F) (Ω := Ω)
  set f := (minpoly F x).map (algebraMap F Ω)
  have hsep : f.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F x)
  have hspl : f.Splits := IsSepClosed.splits_of_separable f hsep
  have hroot (y : Ω) (hy : y ∈ f.roots) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))] at hy
    have := minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)) hy
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    exact (Normal.minpoly_eq_iff_mem_orbit Ω).1 this.symm
  have hx0 : x ∈ f.roots := by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
    exact minpoly.aeval F x
  refine ⟨f.roots.sum, ?_, ?_⟩
  · rw [← neg_neg f.roots.sum, ← hspl.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _),
      Polynomial.nextCoeff_map (algebraMap F Ω).injective]
    exact F.neg_mem (Subtype.mem _)
  · rw [← Multiset.sum_erase hx0, add_sub_cancel_left]
    have hlt (y : Ω) (hy : y ∈ f.roots.erase x) : v y < γ := by
      obtain ⟨hyx, hy⟩ := (Polynomial.nodup_roots hsep).mem_erase_iff.1 hy
      obtain ⟨σ, rfl⟩ := hroot y hy
      exact hconj σ hyx
    exact Valuation.map_multiset_sum_lt v hγ _ hlt

/-- **Separating element.** Let `a` be fixed by the decomposition group of `𝒪` over `F`. Then
some `e`, integral over `𝒪 ∩ F` and fixed by every automorphism fixing `a`, is a unit of `𝒪`
with `σ e` in the maximal ideal for every `σ` with `σ a ≠ a`. -/
theorem exists_isIntegral_separating [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω] {a : Ω}
    (hfix : ∀ σ : 𝒪.decompositionSubgroup F, (σ : Ω ≃ₐ[F] Ω) a = a) :
    ∃ e : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) e ∧
      (∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ e = e) ∧ 𝒪.valuation e = 1 ∧
      ∀ σ : Ω ≃ₐ[F] Ω, σ a ≠ a → 𝒪.valuation (σ e) < 1 := by
  classical
  set R := 𝒪.toSubring ⊓ F.toSubring
  have hle (σ : Ω ≃ₐ[F] Ω) {b : Ω} (hb : IsIntegral R b) : 𝒪.valuation (σ b) ≤ 1 :=
    (valuation_le_one_iff _ _).2
      (mem_of_isIntegral_of_le inf_le_left (isIntegral_algEquiv_apply inf_le_right σ hb))
  have hsep (c : Ω) : ∃ e : Ω, IsIntegral R e ∧ (∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ e = e) ∧
      𝒪.valuation e = 1 ∧ ∀ σ : Ω ≃ₐ[F] Ω, σ a = c → c ≠ a → 𝒪.valuation (σ e) < 1 := by
    by_cases hc : ∃ τ : Ω ≃ₐ[F] Ω, τ a = c ∧ c ≠ a
    · obtain ⟨τ, rfl, hτ⟩ := hc
      obtain ⟨e, he, hfe, hve, hτe⟩ := exists_isIntegral_valuation_apply_lt_one F hfix hτ
      refine ⟨e, he, hfe, hve, fun σ hσ _ ↦ ?_⟩
      have := hfe (τ⁻¹ * σ) (by
        rw [AlgEquiv.mul_apply, hσ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at this
      rwa [this]
    · push Not at hc
      exact ⟨1, isIntegral_one, fun σ _ ↦ map_one σ, map_one _,
        fun σ hσ hca ↦ absurd (hc σ hσ) hca⟩
  choose E hEi hEf hEv hEl using hsep
  set S := ((minpoly F a).aroots Ω).toFinset
  refine ⟨∏ c ∈ S, E c, prod_mem (S := integralClosure R Ω) fun c _ ↦ hEi c,
    fun σ hσ ↦ ?_, ?_, fun σ hσ ↦ ?_⟩
  · rw [map_prod]
    exact Finset.prod_congr rfl fun c _ ↦ hEf c σ hσ
  · rw [map_prod]
    exact Finset.prod_eq_one fun c _ ↦ hEv c
  · have hmem : σ a ∈ S := by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral a), ?_⟩
      rw [← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [← Finset.mul_prod_erase S E hmem, map_mul, map_mul]
    exact mul_lt_one_of_lt_of_le (hEl _ σ rfl hσ)
      (hle σ (prod_mem (S := integralClosure R Ω) fun c _ ↦ hEi c))

/-- **Uniform smallness of powers of conjugates (rank one).** If the valuation is of rank one
(archimedean), then for every `e` and `γ ≠ 0` some power `N` makes `v (σ e) ^ N < γ` for all
conjugates `σ e` of value `< 1`. -/
theorem exists_pow_valuation_apply_lt [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω]
    (hrk : ∀ s t : Ω, t ≠ 0 → 𝒪.valuation s < 1 → ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    (e : Ω) {t : Ω} (ht : t ≠ 0) :
    ∃ N : ℕ, ∀ σ : Ω ≃ₐ[F] Ω, 𝒪.valuation (σ e) < 1 → 𝒪.valuation (σ e) ^ N < 𝒪.valuation t := by
  classical
  have hfin (S : Finset Ω) : ∃ N : ℕ, ∀ r ∈ S, 𝒪.valuation r < 1 →
      𝒪.valuation r ^ N < 𝒪.valuation t := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert r S _ ih =>
      obtain ⟨N₁, hN₁⟩ := ih
      by_cases hr : 𝒪.valuation r < 1
      · obtain ⟨N₂, hN₂⟩ := hrk r t ht hr
        refine ⟨N₁ + N₂, fun r' hr' hr'1 ↦ ?_⟩
        rw [pow_add]
        rcases Finset.mem_insert.1 hr' with rfl | hr'
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one₀ zero_le hr'1.le)) hN₂
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hr'1.le))
            (hN₁ r' hr' hr'1)
      · refine ⟨N₁, fun r' hr' hr'1 ↦ ?_⟩
        rcases Finset.mem_insert.1 hr' with rfl | hr'
        · exact absurd hr'1 hr
        · exact hN₁ r' hr' hr'1
  obtain ⟨N, hN⟩ := hfin ((minpoly F e).aroots Ω).toFinset
  refine ⟨N, fun σ hσ ↦ hN _ ?_ hσ⟩
  rw [Multiset.mem_toFinset, mem_aroots]
  refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral e), ?_⟩
  rw [← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, minpoly.aeval, map_zero]

/-- **Density of `F` in the decomposition field, integral case (rank one).** If `𝒪` has rank
one, every `a ∈ 𝒪` fixed by the decomposition group of `𝒪` over `F` is a limit of elements
of `F ∩ 𝒪`. -/
theorem exists_valuation_sub_lt_of_forall_decompositionSubgroup [IsSepClosed Ω]
    (F : Subfield Ω) [Algebra.IsSeparable F Ω]
    (hrk : ∀ s t : Ω, t ≠ 0 → 𝒪.valuation s < 1 → ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {a : Ω} (ha : a ∈ 𝒪) (hfix : ∀ σ : 𝒪.decompositionSubgroup F, (σ : Ω ≃ₐ[F] Ω) a = a)
    {t : Ω} (ht : t ≠ 0) (ht1 : 𝒪.valuation t ≤ 1) :
    ∃ b ∈ F, 𝒪.valuation (a - b) < 𝒪.valuation t := by
  set R := 𝒪.toSubring ⊓ F.toSubring
  have hle (σ : Ω ≃ₐ[F] Ω) {b : Ω} (hb : IsIntegral R b) : 𝒪.valuation (σ b) ≤ 1 :=
    (valuation_le_one_iff _ _).2
      (mem_of_isIntegral_of_le inf_le_left (isIntegral_algEquiv_apply inf_le_right σ hb))
  have hγ : 𝒪.valuation t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  obtain ⟨e₀, he₀i, he₀f, he₀v, he₀l⟩ := exists_isIntegral_separating F hfix
  obtain ⟨N, hN⟩ := exists_pow_valuation_apply_lt F hrk e₀ ht
  set e := e₀ ^ N
  have hef (σ : Ω ≃ₐ[F] Ω) (hσ : σ a = a) : σ e = e := by
    rw [map_pow, he₀f σ hσ]
  have hev : 𝒪.valuation e = 1 := by rw [map_pow, he₀v, one_pow]
  have hconj {y : Ω} (hy : IsIntegral R y) (hyf : ∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ y = y)
      (σ : Ω ≃ₐ[F] Ω) (hσ : σ (y * e) ≠ y * e) : 𝒪.valuation (σ (y * e)) < 𝒪.valuation t := by
    have hσa : σ a ≠ a := fun h ↦ hσ (by rw [map_mul, hyf σ h, hef σ h])
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle σ hy)) (hN σ (he₀l σ hσa))
  obtain ⟨s, hsi, hsv, hasi, hsf⟩ := exists_isIntegral_mul_isIntegral_of_forall_apply_eq F ha
    (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨c₁, hc₁F, hc₁⟩ := exists_mem_valuation_sub_lt_of_conj 𝒪.valuation hγ
    (hconj hasi fun σ hσ ↦ by rw [map_mul, hσ, hsf σ hσ])
  obtain ⟨c₂, hc₂F, hc₂⟩ := exists_mem_valuation_sub_lt_of_conj 𝒪.valuation hγ (hconj hsi hsf)
  have hv2 : 𝒪.valuation (s * e) = 1 := by rw [map_mul, hsv, hev, one_mul]
  have hc₂v : 𝒪.valuation c₂ = 1 := by
    rw [← add_sub_cancel (s * e) c₂,
      Valuation.map_add_eq_of_lt_left _ (hv2 ▸ lt_of_lt_of_le hc₂ ht1), hv2]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc₂v
    exact zero_ne_one hc₂v
  refine ⟨c₁ / c₂, F.div_mem hc₁F hc₂F, ?_⟩
  have hdiff : a - c₁ / c₂ = (a * (c₂ - s * e) - (c₁ - a * s * e)) / c₂ := by
    field_simp
    ring
  have h1 : 𝒪.valuation (a * (c₂ - s * e)) < 𝒪.valuation t := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((valuation_le_one_iff _ _).2 ha)) hc₂
  rw [hdiff, map_div₀, hc₂v, div_one]
  exact Valuation.map_sub_lt _ h1 hc₁

/-- **Density of `F` in the decomposition field (rank one).** If `𝒪` has rank one, every
element `z` of the decomposition field `Z` of `𝒪` over `F` is a limit of elements of `F`:
for every `t ≠ 0` there is `f ∈ F` with `v (z - f) < v t`. In other words, the henselisation
`Z` of `F` lies in the completion of `F`. -/
theorem exists_valuation_sub_lt_of_mem_fixedField [IsSepClosed Ω]
    (F : Subfield Ω) [Algebra.IsSeparable F Ω]
    (hrk : ∀ s t : Ω, t ≠ 0 → 𝒪.valuation s < 1 → ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {z : Ω} (hz : z ∈ IntermediateField.fixedField (𝒪.decompositionSubgroup F))
    {t : Ω} (ht : t ≠ 0) :
    ∃ f ∈ F, 𝒪.valuation (z - f) < 𝒪.valuation t := by
  rw [IntermediateField.mem_fixedField_iff] at hz
  have hfix (y : Ω) (hy : ∀ σ ∈ 𝒪.decompositionSubgroup F, σ • y = y)
      (σ : 𝒪.decompositionSubgroup F) : (σ : Ω ≃ₐ[F] Ω) y = y :=
    hy σ σ.2
  -- `t' = t` if `v t ≤ 1`, else `1`
  obtain ⟨t', ht'0, ht'1, ht't⟩ : ∃ t' : Ω, t' ≠ 0 ∧ 𝒪.valuation t' ≤ 1 ∧
      𝒪.valuation t' ≤ 𝒪.valuation t := by
    rcases le_total (𝒪.valuation t) 1 with h | h
    · exact ⟨t, ht, h, le_rfl⟩
    · exact ⟨1, one_ne_zero, by rw [map_one], by rwa [map_one]⟩
  by_cases hz𝒪 : z ∈ 𝒪
  · obtain ⟨b, hbF, hb⟩ :=
      exists_valuation_sub_lt_of_forall_decompositionSubgroup F hrk hz𝒪 (hfix z hz) ht'0 ht'1
    exact ⟨b, hbF, lt_of_lt_of_le hb ht't⟩
  -- otherwise approximate `w = z⁻¹ ∈ 𝔪`
  have hz0 : z ≠ 0 := fun h ↦ hz𝒪 (h ▸ zero_mem 𝒪)
  have hw1 : 𝒪.valuation z⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).2 hz0)]
    exact lt_of_not_ge fun h ↦ hz𝒪 ((valuation_le_one_iff _ _).1 h)
  have hw0 : 𝒪.valuation z⁻¹ ≠ 0 := (Valuation.ne_zero_iff _).2 (inv_ne_zero hz0)
  have hwfix (σ : 𝒪.decompositionSubgroup F) : (σ : Ω ≃ₐ[F] Ω) z⁻¹ = z⁻¹ := by
    rw [map_inv₀, hfix z hz σ]
  have ht₀1 : 𝒪.valuation (t' * z⁻¹ ^ 2) ≤ 𝒪.valuation z⁻¹ := by
    rw [map_mul, map_pow, sq, ← mul_assoc]
    exact mul_le_of_le_one_left' (mul_le_one' ht'1 hw1.le)
  obtain ⟨b, hbF, hb⟩ := exists_valuation_sub_lt_of_forall_decompositionSubgroup F hrk
    ((valuation_le_one_iff _ _).1 hw1.le) hwfix
    (mul_ne_zero ht'0 (pow_ne_zero 2 (inv_ne_zero hz0))) (ht₀1.trans hw1.le)
  have hbv : 𝒪.valuation b = 𝒪.valuation z⁻¹ := by
    rw [← sub_sub_cancel z⁻¹ b, Valuation.map_sub_eq_of_lt_left _ (lt_of_lt_of_le hb ht₀1)]
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hbv
    exact hw0 hbv.symm
  refine ⟨b⁻¹, F.inv_mem hbF, lt_of_lt_of_le ?_ ht't⟩
  have hdiff : z - b⁻¹ = (b - z⁻¹) / (z⁻¹ * b) := by
    field_simp
  have hpos : 0 < 𝒪.valuation z⁻¹ * 𝒪.valuation z⁻¹ :=
    mul_pos (zero_lt_iff.2 hw0) (zero_lt_iff.2 hw0)
  rw [map_mul, map_pow, sq] at hb
  rw [hdiff, map_div₀, map_mul, hbv, Valuation.map_sub_swap, div_lt_iff₀ hpos]
  exact hb

end ValuationSubring
