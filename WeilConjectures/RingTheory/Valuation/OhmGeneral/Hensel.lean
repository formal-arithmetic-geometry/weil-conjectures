/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral
public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.RingTheory.Valuation.KummerHensel

/-!
# Hensel properties of the inertia field

Let `Ω` be a separably closed field, `𝒪` a valuation subring of `Ω` with residue characteristic
`p` and `F ⊆ Ω` a subfield. Let `L` be the inertia field of `𝒪` over `F`.

* `ValuationSubring.exists_pow_sub_self_eq_of_mem_inertiaField`: in characteristic `p`, every
  Artin–Schreier equation `θ ^ p - θ = b` with `b ∈ L ∩ 𝒪` has a solution in `L`.
* `ValuationSubring.exists_pow_eq_one_add_of_mem_inertiaField`: if `y ∈ L` is Kummer-negligible,
  then `1 + y` is a `p`-th power in `L`.

In both cases a root in `Ω` exists since the polynomial is separable, and every element `σ` of
the inertia group maps this root to a root which is residually close to it; since distinct roots
are residually far apart, `σ` fixes the root.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω) {F : Subfield Ω}

/-- An element of the decomposition group maps `𝒪` into itself. -/
theorem decompositionSubgroup_apply_mem (σ : 𝒪.decompositionSubgroup F) {x : Ω} (hx : x ∈ 𝒪) :
    (σ : Ω ≃ₐ[F] Ω) x ∈ 𝒪 :=
  (σ • (⟨x, hx⟩ : 𝒪)).2

/-- An element of the inertia group acts trivially on the residue field. -/
theorem valuation_inertiaSubgroup_apply_sub_lt_one {σ : 𝒪.decompositionSubgroup F}
    (hσ : σ ∈ 𝒪.inertiaSubgroup F) {x : Ω} (hx : x ∈ 𝒪) :
    𝒪.valuation ((σ : Ω ≃ₐ[F] Ω) x - x) < 1 := by
  rw [inertiaSubgroup, MonoidHom.mem_ker] at hσ
  have h := DFunLike.congr_fun hσ (residue 𝒪 ⟨x, hx⟩)
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply,
    ← IsLocalRing.ResidueField.residue_smul,
    RingAut.one_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, valuation_lt_one_iff] at h
  exact h


/-- Membership in the inertia field: being fixed by every element of the inertia group. -/
theorem mem_inertiaField_iff {x : Ω} :
    x ∈ 𝒪.inertiaField F ↔ ∀ σ ∈ 𝒪.inertiaSubgroup F, (σ : Ω ≃ₐ[F] Ω) x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]
  refine ⟨fun h σ hσ => h _ (Subgroup.mem_map_of_mem _ hσ), fun h g hg => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hg
  exact h σ hσ

/-- An element `θ ∈ 𝒪` such that every element of the inertia group maps `θ` to a root of `f`,
where `f` has coefficients in `𝒪` and `f'(θ)` is a unit, lies in the inertia field. -/
theorem mem_inertiaField_of_isRoot {f : Ω[X]} (hf𝒪 : ∀ i, f.coeff i ∈ 𝒪) {θ : Ω} (hθ : θ ∈ 𝒪)
    (hfθ : f.IsRoot θ) (hf' : 𝒪.valuation (f.derivative.eval θ) = 1)
    (hσf : ∀ σ ∈ 𝒪.inertiaSubgroup F, f.IsRoot ((σ : Ω ≃ₐ[F] Ω) θ)) :
    θ ∈ 𝒪.inertiaField F := by
  rw [mem_inertiaField_iff]
  intro σ hσ
  exact eq_of_isRoot_of_valuation_sub_lt_one 𝒪 hf𝒪 hθ (decompositionSubgroup_apply_mem 𝒪 σ hθ)
    hfθ (hσf σ hσ) hf' (valuation_inertiaSubgroup_apply_sub_lt_one 𝒪 hσ hθ)

/-- **Artin–Schreier equations over the inertia field.** In characteristic `p`, if `b` lies in
the inertia field `L` of `𝒪` over `F` and in `𝒪`, then `θ ^ p - θ = b` has a solution in `L`. -/
theorem exists_pow_sub_self_eq_of_mem_inertiaField [IsSepClosed Ω] (p : ℕ) [hp : Fact p.Prime]
    [CharP Ω p] {b : Ω} (hbL : b ∈ 𝒪.inertiaField F) (hb : 𝒪.valuation b ≤ 1) :
    ∃ θ ∈ 𝒪.inertiaField F, θ ^ p - θ = b := by
  have hp1 := hp.out.one_lt
  have hderiv (x : Ω) : (X ^ p - X - C b : Ω[X]).derivative.eval x = -1 := by
    simp [derivative_X_pow]
  have hsep : (X ^ p - X - C b : Ω[X]).Separable := by
    rw [Separable]
    refine ⟨0, -1, ?_⟩
    rw [derivative_sub, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
      CharP.cast_eq_zero, C_0, zero_mul]
    ring
  have hdeg : (X ^ p - X - C b : Ω[X]).degree ≠ 0 := by
    rw [sub_sub, degree_sub_eq_left_of_degree_lt, degree_X_pow]
    · exact_mod_cast hp.out.ne_zero
    · rw [degree_X_pow, degree_X_add_C]
      exact_mod_cast hp1
  obtain ⟨θ, hθ⟩ := IsSepClosed.exists_root _ hdeg hsep
  have hθ' : θ ^ p = θ + b := by
    rw [← sub_eq_zero, ← sub_sub]
    simpa using hθ.eq_zero
  have hθ𝒪 : θ ∈ 𝒪 := by
    rw [← valuation_le_one_iff]
    by_contra h
    rw [not_le] at h
    have h1 : 𝒪.valuation (θ ^ p) ≤ 𝒪.valuation θ := by
      rw [hθ']
      exact (Valuation.map_add _ _ _).trans (max_le le_rfl (hb.trans h.le))
    rw [map_pow] at h1
    exact h1.not_gt (lt_self_pow₀ h hp1)
  refine ⟨θ, mem_inertiaField_of_isRoot 𝒪 (coeff_X_pow_sub_X_sub_C_mem p
    ((valuation_le_one_iff _ _).1 hb)) hθ𝒪 hθ (by rw [hderiv, Valuation.map_neg, map_one])
    fun σ hσ => ?_, by rw [hθ']; ring⟩
  have hσb : (σ : Ω ≃ₐ[F] Ω) b = b := (mem_inertiaField_iff 𝒪).1 hbL σ hσ
  have := congrArg (σ : Ω ≃ₐ[F] Ω) hθ.eq_zero
  simpa [hσb] using this

/-- For `a, b ∈ 𝒪`, `a ≡ b` modulo the maximal ideal iff their residues agree. -/
theorem valuation_sub_lt_one_iff_residue_eq {a b : Ω} (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) :
    𝒪.valuation (a - b) < 1 ↔ residue 𝒪 ⟨a, ha⟩ = residue 𝒪 ⟨b, hb⟩ := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, valuation_lt_one_iff]
  rfl

/-- If the residue characteristic is `p` and `a ^ p ≡ b ^ p` modulo the maximal ideal, then
`a ≡ b`. -/
theorem valuation_sub_lt_one_of_pow (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] {a b : Ω}
    (ha : a ∈ 𝒪) (hb : b ∈ 𝒪) (h : 𝒪.valuation (a ^ p - b ^ p) < 1) :
    𝒪.valuation (a - b) < 1 := by
  rw [valuation_sub_lt_one_iff_residue_eq 𝒪 ha hb]
  rw [valuation_sub_lt_one_iff_residue_eq 𝒪 (pow_mem ha p) (pow_mem hb p)] at h
  refine frobenius_inj (ResidueField 𝒪) p ?_
  rw [frobenius_def, frobenius_def, ← map_pow, ← map_pow]
  exact h

/-- A monic split polynomial of positive degree `n` has a root `r` with
`v(x - r) ^ n ≤ v(f(x))`. -/
theorem exists_isRoot_valuation_sub_pow_le {f : Ω[X]} (hf : f.Splits) (hm : f.Monic)
    (hdeg : f.natDegree ≠ 0) (x : Ω) :
    ∃ r, f.IsRoot r ∧ 𝒪.valuation (x - r) ^ f.natDegree ≤ 𝒪.valuation (f.eval x) := by
  have hroots : f.roots ≠ 0 := by
    intro h
    rw [hf.natDegree_eq_card_roots, h, Multiset.card_zero] at hdeg
    exact hdeg rfl
  obtain ⟨r, hr, hmin⟩ := Multiset.exists_min_image (fun r => 𝒪.valuation (x - r)) hroots
  refine ⟨r, (mem_roots hm.ne_zero).1 hr, ?_⟩
  rw [hf.eval_eq_prod_roots, hm.leadingCoeff, one_mul, map_multiset_prod, Multiset.map_map,
    hf.natDegree_eq_card_roots, ← Multiset.card_map (fun r => 𝒪.valuation (x - r)) f.roots]
  refine Multiset.pow_card_le_prod fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 ha
  exact hmin t ht

/-- **Kummer equations over the inertia field.** If the residue characteristic of `𝒪` is `p` and
`y` lies in the inertia field `L` of `𝒪` over `F` and is Kummer-negligible, i.e.
`v(y) ^ (p - 1) ≤ v(p) ^ p`, then `1 + y` is a `p`-th power in `L`. -/
theorem exists_pow_eq_one_add_of_mem_inertiaField [IsSepClosed Ω] (p : ℕ) [hp : Fact p.Prime]
    [CharP (ResidueField 𝒪) p] {y : Ω} (hyL : y ∈ 𝒪.inertiaField F)
    (hy : 𝒪.valuation.IsKummerNegligible p y) :
    ∃ z ∈ 𝒪.inertiaField F, z ^ p = 1 + y := by
  have hp2 := hp.out.two_le
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨1, (𝒪.inertiaField F).one_mem, by simp⟩
  have hp1 : 𝒪.valuation (p : Ω) < 1 := by
    have : (p : 𝒪) ∈ maximalIdeal 𝒪 := by
      rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
    simpa using (valuation_lt_one_iff 𝒪 _).1 this
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    rw [Valuation.IsKummerNegligible, h, map_zero, zero_pow (by omega), le_zero_iff,
      pow_eq_zero_iff (by omega), Valuation.zero_iff] at hy
    exact hy0 hy
  have hpm1 : ((p - 1 : ℕ) : Ω) ≠ 0 := by
    intro h
    have : ((p - 1 : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := by
      rw [valuation_lt_one_iff]
      simp [h]
    rw [← residue_eq_zero_iff, map_natCast, Nat.cast_sub hp.out.one_le, CharP.cast_eq_zero,
      Nat.cast_one, zero_sub, neg_eq_zero] at this
    exact one_ne_zero this
  have : NeZero ((p - 1 : ℕ) : Ω) := ⟨hpm1⟩
  obtain ⟨ϖ, hϖ⟩ := IsSepClosed.exists_pow_nat_eq (-(p : Ω)) (p - 1)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), eq_comm, neg_eq_zero] at hϖ
    exact hp0 hϖ
  have hvϖ : 𝒪.valuation ϖ ^ (p - 1) = 𝒪.valuation (p : Ω) := by
    rw [← map_pow, hϖ, Valuation.map_neg]
  have hvϖ0 : 0 < 𝒪.valuation ϖ := (Valuation.pos_iff _).2 hϖ0
  have hvϖ1 : 𝒪.valuation ϖ < 1 := by
    by_contra h
    rw [not_lt] at h
    exact hp1.not_ge (hvϖ ▸ one_le_pow₀ h)
  have hvy : 𝒪.valuation y ≤ 𝒪.valuation ϖ ^ p := by
    have := valuation_div_pow_le_one_of_isKummerNegligible 𝒪 p hϖ0 hϖ hy
    rwa [map_div₀, map_pow, div_le_one₀ (pow_pos hvϖ0 _)] at this
  have hvy1 : 𝒪.valuation y < 1 := hvy.trans_lt (pow_lt_one₀ zero_le hvϖ1 (by omega))
  have hvy0 : 0 < 𝒪.valuation y := (Valuation.pos_iff _).2 hy0
  -- the auxiliary polynomial `g`, whose roots are the `(w - 1) / ϖ` for `w ^ p = 1 + y`
  have hc : y / ϖ ^ p ∈ 𝒪 := (valuation_le_one_iff _ _).1
    (valuation_div_pow_le_one_of_isKummerNegligible 𝒪 p hϖ0 hϖ hy)
  set g : Ω[X] := (X + C ϖ⁻¹) ^ p - C ((1 + y) / ϖ ^ p) with hg
  have hD := valuation_coeff_kummer_sub_lt_one 𝒪 p hp1 hϖ0 hϖ y
  have hg𝒪 (i : ℕ) : g.coeff i ∈ 𝒪 := by
    rw [← sub_add_cancel g (X ^ p - X - C (y / ϖ ^ p)), coeff_add]
    exact AddMemClass.add_mem ((valuation_le_one_iff _ _).1 (hD i).le)
      (coeff_X_pow_sub_X_sub_C_mem p hc i)
  -- properties of `(w - 1) / ϖ` for a root `w` close to `1`
  have hroot {w : Ω} (hw : w ^ p = 1 + y) (hwv : 𝒪.valuation (w - 1) ^ p ≤ 𝒪.valuation y) :
      (w - 1) / ϖ ∈ 𝒪 ∧ g.IsRoot ((w - 1) / ϖ) ∧
        𝒪.valuation (g.derivative.eval ((w - 1) / ϖ)) = 1 := by
    have hw1 : 𝒪.valuation w = 1 := by
      rw [← pow_eq_one_iff_left (by omega : p ≠ 0), ← map_pow, hw]
      exact Valuation.map_one_add_of_lt _ hvy1
    have hsw : (w - 1) / ϖ + ϖ⁻¹ = w / ϖ := by
      field_simp
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [← valuation_le_one_iff, map_div₀, div_le_one₀ hvϖ0]
      exact (pow_le_pow_iff_left₀ zero_le zero_le (by omega)).1 (hwv.trans hvy)
    · rw [IsRoot, hg, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_C, hsw, div_pow, hw,
        sub_self]
    · rw [hg, derivative_sub, derivative_C, sub_zero, derivative_X_add_C_pow, eval_mul, eval_C,
        eval_pow, eval_add, eval_X, eval_C, hsw, map_mul, map_pow, map_div₀, hw1, one_div,
        inv_pow, ← hvϖ]
      exact mul_inv_cancel₀ (pow_ne_zero _ hvϖ0.ne')
  -- a root of `X ^ p - (1 + y)` close to `1`
  have hfsep : (X ^ p - C (1 + y) : Ω[X]).Separable :=
    separable_X_pow_sub_C _ hp0 fun h => by
      have := Valuation.map_one_add_of_lt _ hvy1
      rw [h, map_zero] at this
      exact zero_ne_one this
  obtain ⟨z, hz, hzv⟩ := exists_isRoot_valuation_sub_pow_le 𝒪
    (IsSepClosed.splits_of_separable _ hfsep) (monic_X_pow_sub_C _ (by omega))
    (by rw [natDegree_X_pow_sub_C]; omega) 1
  rw [natDegree_X_pow_sub_C, Valuation.map_sub_swap] at hzv
  have hzp : z ^ p = 1 + y := by
    rw [← sub_eq_zero]
    simpa using hz.eq_zero
  have hzv' : 𝒪.valuation (z - 1) ^ p ≤ 𝒪.valuation y := by
    simpa [Valuation.map_neg] using hzv
  obtain ⟨hs, hgs, hg's⟩ := hroot hzp hzv'
  refine ⟨z, (mem_inertiaField_iff 𝒪).2 fun σ hσ => ?_, hzp⟩
  set w := (σ : Ω ≃ₐ[F] Ω) z with hwdef
  have hσy : (σ : Ω ≃ₐ[F] Ω) y = y := (mem_inertiaField_iff 𝒪).1 hyL σ hσ
  have hwp : w ^ p = 1 + y := by
    rw [hwdef, ← map_pow, hzp, map_add, map_one, hσy]
  -- `x = (z - 1) ^ p / y` is integral, and `σ x = (w - 1) ^ p / y`
  have hx : (z - 1) ^ p / y ∈ 𝒪 := by
    rw [← valuation_le_one_iff, map_div₀, map_pow, div_le_one₀ hvy0]
    exact hzv'
  have hσx : (σ : Ω ≃ₐ[F] Ω) ((z - 1) ^ p / y) = (w - 1) ^ p / y := by
    rw [map_div₀, map_pow, map_sub, map_one, hσy]
  have hwv : 𝒪.valuation (w - 1) ^ p ≤ 𝒪.valuation y := by
    have := decompositionSubgroup_apply_mem 𝒪 σ hx
    rwa [hσx, ← valuation_le_one_iff, map_div₀, map_pow, div_le_one₀ hvy0] at this
  obtain ⟨hs', hgs', -⟩ := hroot hwp hwv
  have hclose : 𝒪.valuation ((w - 1) / ϖ - (z - 1) / ϖ) < 1 := by
    rcases hvy.lt_or_eq with hlt | heq
    · have hsmall {u : Ω} (hu : 𝒪.valuation (u - 1) ^ p ≤ 𝒪.valuation y) :
          𝒪.valuation ((u - 1) / ϖ) < 1 := by
        rw [map_div₀, div_lt_one₀ hvϖ0]
        exact (pow_lt_pow_iff_left₀ zero_le zero_le (by omega)).1 (hu.trans_lt hlt)
      exact Valuation.map_sub_lt _ (hsmall hwv) (hsmall hzv')
    · refine valuation_sub_lt_one_of_pow 𝒪 p hs' hs ?_
      have h := valuation_inertiaSubgroup_apply_sub_lt_one 𝒪 hσ hx
      have hid : (w - 1) ^ p / y - (z - 1) ^ p / y =
          (((w - 1) / ϖ) ^ p - ((z - 1) / ϖ) ^ p) * (ϖ ^ p / y) := by
        rw [div_pow, div_pow, sub_mul, div_mul_div_cancel₀ (pow_ne_zero _ hϖ0),
          div_mul_div_cancel₀ (pow_ne_zero _ hϖ0)]
      rwa [hσx, hid, map_mul, map_div₀, map_pow, heq, div_self (pow_ne_zero _ hvϖ0.ne'),
        mul_one] at h
  have hsw := eq_of_isRoot_of_valuation_sub_lt_one 𝒪 hg𝒪 hs hs' hgs hgs' hg's hclose
  rw [div_left_inj' hϖ0, sub_left_inj] at hsw
  exact hsw
end ValuationSubring
