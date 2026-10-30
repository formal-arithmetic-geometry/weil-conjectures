/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral.Residue
public import WeilConjectures.RingTheory.Valuation.OhmGeneral.Hensel
public import WeilConjectures.RingTheory.Valuation.OhmGeneral.Decomposition

/-!
# Towards (R3): exploratory lemmas
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped Pointwise

namespace Polynomial

variable {A : Type*} [CommRing A]

lemma coeff_iterate_divX (f : A[X]) (d n : ℕ) : (divX^[d] f).coeff n = f.coeff (n + d) := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', coeff_divX, ih]
    congr 1
    omega

lemma iterate_divX_eq (f : A[X]) (d : ℕ) :
    divX^[d] f = divX^[d + 1] f * X + C (f.coeff d) := by
  have h := divX_mul_X_add (divX^[d] f)
  rw [coeff_iterate_divX, zero_add] at h
  rw [Function.iterate_succ_apply']
  exact h.symm

lemma degree_sub_X_pow_mul_iterate_divX_lt (f : A[X]) (d : ℕ) :
    (f - X ^ d * divX^[d] f).degree < (d : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_sub, coeff_X_pow_mul', if_pos hn, coeff_iterate_divX, Nat.sub_add_cancel hn, sub_self]

end Polynomial

section Integral

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- If `y` is a root of `f = ∑ aᵢ Xⁱ` and `w_d = ∑_{i ≥ d} aᵢ y^{i - d}` is integral, then so is
`y * w_d`. -/
lemma isIntegral_mul_aeval_iterate_divX {f : A[X]} {y : S} (hf : aeval y f = 0) (d : ℕ)
    (hw : IsIntegral A (aeval y (divX^[d] f))) : IsIntegral A (y * aeval y (divX^[d] f)) := by
  set R := integralClosure A S
  set w : R := ⟨_, hw⟩
  rcases eq_or_ne w 0 with h0 | h0
  · have : aeval y (divX^[d] f) = 0 := congrArg Subtype.val h0
    rw [this, mul_zero]
    exact isIntegral_zero
  set P : R[X] := C w * X ^ d + (f - X ^ d * divX^[d] f).map (algebraMap A R)
  have hP : aeval y P = 0 := by
    simp only [P, map_add, map_mul, aeval_C, map_pow, aeval_X, aeval_map_algebraMap, map_sub, hf]
    simp [w, R, mul_comm]
  have hlt : ((f - X ^ d * divX^[d] f).map (algebraMap A R)).degree < (C w * X ^ d).degree := by
    rw [degree_C_mul_X_pow d h0]
    exact (degree_map_le).trans_lt (degree_sub_X_pow_mul_iterate_divX_lt f d)
  have hlc : P.leadingCoeff = w := by
    rw [leadingCoeff_add_of_degree_lt' hlt, leadingCoeff_C_mul_X_pow]
  have := isIntegral_leadingCoeff_smul P y hP
  rw [hlc, Subalgebra.smul_def] at this
  rw [mul_comm]
  exact isIntegral_trans (R := A) _ this

/-- If `y` is a root of `f = ∑ aᵢ Xⁱ`, then every `w_d = ∑_{i ≥ d} aᵢ y^{i - d}` is integral. -/
lemma isIntegral_aeval_iterate_divX {f : A[X]} {y : S} (hf : aeval y f = 0) (d : ℕ) :
    IsIntegral A (aeval y (divX^[d] f)) := by
  suffices h : ∀ k, IsIntegral A (aeval y (divX^[f.natDegree + 1 - k] f)) by
    by_cases hd : d ≤ f.natDegree + 1
    · have := h (f.natDegree + 1 - d)
      rwa [Nat.sub_sub_self hd] at this
    · have h0 : divX^[d] f = 0 := by
        ext n
        rw [coeff_iterate_divX, coeff_zero]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0, map_zero]
      exact isIntegral_zero
  intro k
  induction k with
  | zero =>
    have h0 : divX^[f.natDegree + 1 - 0] f = 0 := by
      ext n
      rw [coeff_iterate_divX, coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0, map_zero]
    exact isIntegral_zero
  | succ k ih =>
    by_cases hk : f.natDegree + 1 ≤ k
    · have : f.natDegree + 1 - (k + 1) = f.natDegree + 1 - k := by omega
      rwa [this]
    · have : f.natDegree + 1 - k = f.natDegree + 1 - (k + 1) + 1 := by omega
      rw [this] at ih
      rw [iterate_divX_eq f (f.natDegree + 1 - (k + 1)), map_add, map_mul, aeval_X, aeval_C,
        mul_comm]
      exact (isIntegral_mul_aeval_iterate_divX hf _ ih).add isIntegral_algebraMap

end Integral

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- An element integral over a subring of `𝒪` lies in `𝒪`. -/
lemma mem_of_isIntegral_of_le {R : Subring Ω} (hR : R ≤ 𝒪.toSubring) {b : Ω}
    (hb : IsIntegral R b) : b ∈ 𝒪 := by
  let : Algebra R 𝒪 := (Subring.inclusion hR).toAlgebra
  have : IsScalarTower R 𝒪 Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hv : 𝒪.valuation.Integers 𝒪 :=
    ⟨Subtype.val_injective, fun r ↦ 𝒪.valuation_le_one r,
      fun x hx ↦ ⟨⟨x, (𝒪.valuation_le_one_iff x).1 hx⟩, rfl⟩⟩
  exact (𝒪.valuation_le_one_iff b).1 (hv.mem_of_integral (hb.tower_top (A := 𝒪)))

/-- **Key lemma for the dictionary between `𝒪` and the integral closure.** Let `y ∈ 𝒪` be
algebraic over a subfield `F`. Then `y = t / s` with `s`, `t` integral over `𝒪 ∩ F` and `s` a
unit of `𝒪`. -/
theorem exists_isIntegral_mul_isIntegral (F : Subfield Ω) {y : Ω} (hy : y ∈ 𝒪)
    (halg : IsAlgebraic F y) :
    ∃ s : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) s ∧ 𝒪.valuation s = 1 ∧
      IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) (y * s) := by
  set R := 𝒪.toSubring ⊓ F.toSubring
  obtain ⟨g, hg0, hg⟩ := halg
  set g' : Ω[X] := g.map (algebraMap F Ω)
  have hg'0 : g' ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap F Ω).injective).2 hg0
  have hg' : aeval y g' = 0 := by
    rw [aeval_map_algebraMap]
    exact hg
  obtain ⟨i0, hi0, hmax⟩ := g'.support.exists_max_image (fun i ↦ 𝒪.valuation (g'.coeff i))
    (nonempty_support_iff.2 hg'0)
  have hc0 : g'.coeff i0 ≠ 0 := mem_support_iff.1 hi0
  have hvc0 : 𝒪.valuation (g'.coeff i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  set h : Ω[X] := C (g'.coeff i0)⁻¹ * g' with hh
  have hhF (n : ℕ) : h.coeff n ∈ F := by
    rw [hh, coeff_C_mul, coeff_map, coeff_map]
    exact F.mul_mem (F.inv_mem (g.coeff i0).2) (g.coeff n).2
  have hhv (n : ℕ) : 𝒪.valuation (h.coeff n) ≤ 1 := by
    rw [hh, coeff_C_mul, map_mul, map_inv₀]
    by_cases hn : n ∈ g'.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.2 hvc0)]
      exact hmax n hn
    · rw [notMem_support_iff.1 hn, map_zero, mul_zero]
      exact zero_le
  have hhR (n : ℕ) : h.coeff n ∈ R :=
    Subring.mem_inf.2 ⟨(𝒪.valuation_le_one_iff _).1 (hhv n), hhF n⟩
  set f := h.toSubring R fun _ hx ↦ by
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact hhR n
  have hfc (n : ℕ) : ((f.coeff n : R) : Ω) = h.coeff n := coeff_toSubring _ _ _
  have hf : aeval y f = 0 := by
    have hmap : f.map (algebraMap R Ω) = h := by
      ext n
      rw [coeff_map]
      exact hfc n
    rw [aeval_def, eval₂_eq_eval_map, hmap, hh, eval_mul, eval_C,
      ← coe_aeval_eq_eval, hg', mul_zero]
  -- the largest index `j` with a unit coefficient
  set J := h.support.filter fun n ↦ 𝒪.valuation (h.coeff n) = 1
  have hi0J : i0 ∈ J := by
    have h1 : h.coeff i0 = 1 := by rw [hh, coeff_C_mul, inv_mul_cancel₀ hc0]
    refine Finset.mem_filter.2 ⟨mem_support_iff.2 ?_, ?_⟩ <;> simp [h1]
  set j := J.max' ⟨i0, hi0J⟩
  have hj : 𝒪.valuation (h.coeff j) = 1 := (Finset.mem_filter.1 (J.max'_mem ⟨i0, hi0J⟩)).2
  have hgt (n : ℕ) (hn : j < n) : 𝒪.valuation (h.coeff n) < 1 := by
    refine lt_of_le_of_ne (hhv n) fun heq ↦ ?_
    have hn0 : h.coeff n ≠ 0 := by
      intro h0
      rw [h0, map_zero] at heq
      exact zero_ne_one heq
    have := J.le_max' n (Finset.mem_filter.2 ⟨mem_support_iff.2 hn0, heq⟩)
    omega
  have hs : aeval y (divX^[j] f) = aeval y (divX^[j + 1] f) * y + h.coeff j := by
    rw [iterate_divX_eq f j, map_add, map_mul, aeval_X, aeval_C]
    rw [← hfc]
    rfl
  have hw : 𝒪.valuation (aeval y (divX^[j + 1] f)) < 1 := by
    rw [aeval_eq_sum_range]
    refine Valuation.map_sum_lt _ one_ne_zero fun n _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    have h1 : 𝒪.valuation (algebraMap R Ω ((divX^[j + 1] f).coeff n)) < 1 := by
      have := hfc (n + (j + 1))
      rw [← coeff_iterate_divX] at this
      exact (congrArg 𝒪.valuation this).trans_lt (hgt _ (by omega))
    exact mul_lt_one_of_lt_of_le h1 (pow_le_one' ((𝒪.valuation_le_one_iff y).2 hy) n)
  refine ⟨aeval y (divX^[j] f), isIntegral_aeval_iterate_divX hf j, ?_,
    isIntegral_mul_aeval_iterate_divX hf j (isIntegral_aeval_iterate_divX hf j)⟩
  have hlt : 𝒪.valuation (aeval y (divX^[j + 1] f) * y) < 𝒪.valuation (h.coeff j) := by
    rw [map_mul, hj]
    exact mul_lt_one_of_lt_of_le hw ((𝒪.valuation_le_one_iff y).2 hy)
  rw [hs, add_comm, Valuation.map_add_eq_of_lt_left _ hlt, hj]

/-- Variant of `exists_isIntegral_mul_isIntegral` remembering that the denominator `s` is a
polynomial in `y` over `𝒪 ∩ F`: every automorphism of `Ω / F` fixing `y` fixes `s`. -/
theorem exists_isIntegral_mul_isIntegral_of_forall_apply_eq (F : Subfield Ω) {y : Ω} (hy : y ∈ 𝒪)
    (halg : IsAlgebraic F y) :
    ∃ s : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) s ∧ 𝒪.valuation s = 1 ∧
      IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) (y * s) ∧
      ∀ σ : Ω ≃ₐ[F] Ω, σ y = y → σ s = s := by
  set R := 𝒪.toSubring ⊓ F.toSubring
  obtain ⟨g, hg0, hg⟩ := halg
  set g' : Ω[X] := g.map (algebraMap F Ω)
  have hg'0 : g' ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap F Ω).injective).2 hg0
  have hg' : aeval y g' = 0 := by
    rw [aeval_map_algebraMap]
    exact hg
  obtain ⟨i0, hi0, hmax⟩ := g'.support.exists_max_image (fun i ↦ 𝒪.valuation (g'.coeff i))
    (nonempty_support_iff.2 hg'0)
  have hc0 : g'.coeff i0 ≠ 0 := mem_support_iff.1 hi0
  have hvc0 : 𝒪.valuation (g'.coeff i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  set h : Ω[X] := C (g'.coeff i0)⁻¹ * g' with hh
  have hhF (n : ℕ) : h.coeff n ∈ F := by
    rw [hh, coeff_C_mul, coeff_map, coeff_map]
    exact F.mul_mem (F.inv_mem (g.coeff i0).2) (g.coeff n).2
  have hhv (n : ℕ) : 𝒪.valuation (h.coeff n) ≤ 1 := by
    rw [hh, coeff_C_mul, map_mul, map_inv₀]
    by_cases hn : n ∈ g'.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.2 hvc0)]
      exact hmax n hn
    · rw [notMem_support_iff.1 hn, map_zero, mul_zero]
      exact zero_le
  have hhR (n : ℕ) : h.coeff n ∈ R :=
    Subring.mem_inf.2 ⟨(𝒪.valuation_le_one_iff _).1 (hhv n), hhF n⟩
  set f := h.toSubring R fun _ hx ↦ by
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact hhR n
  have hfc (n : ℕ) : ((f.coeff n : R) : Ω) = h.coeff n := coeff_toSubring _ _ _
  have hf : aeval y f = 0 := by
    have hmap : f.map (algebraMap R Ω) = h := by
      ext n
      rw [coeff_map]
      exact hfc n
    rw [aeval_def, eval₂_eq_eval_map, hmap, hh, eval_mul, eval_C,
      ← coe_aeval_eq_eval, hg', mul_zero]
  -- the largest index `j` with a unit coefficient
  set J := h.support.filter fun n ↦ 𝒪.valuation (h.coeff n) = 1
  have hi0J : i0 ∈ J := by
    have h1 : h.coeff i0 = 1 := by rw [hh, coeff_C_mul, inv_mul_cancel₀ hc0]
    refine Finset.mem_filter.2 ⟨mem_support_iff.2 ?_, ?_⟩ <;> simp [h1]
  set j := J.max' ⟨i0, hi0J⟩
  have hj : 𝒪.valuation (h.coeff j) = 1 := (Finset.mem_filter.1 (J.max'_mem ⟨i0, hi0J⟩)).2
  have hgt (n : ℕ) (hn : j < n) : 𝒪.valuation (h.coeff n) < 1 := by
    refine lt_of_le_of_ne (hhv n) fun heq ↦ ?_
    have hn0 : h.coeff n ≠ 0 := by
      intro h0
      rw [h0, map_zero] at heq
      exact zero_ne_one heq
    have := J.le_max' n (Finset.mem_filter.2 ⟨mem_support_iff.2 hn0, heq⟩)
    omega
  have hs : aeval y (divX^[j] f) = aeval y (divX^[j + 1] f) * y + h.coeff j := by
    rw [iterate_divX_eq f j, map_add, map_mul, aeval_X, aeval_C]
    rw [← hfc]
    rfl
  have hw : 𝒪.valuation (aeval y (divX^[j + 1] f)) < 1 := by
    rw [aeval_eq_sum_range]
    refine Valuation.map_sum_lt _ one_ne_zero fun n _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    have h1 : 𝒪.valuation (algebraMap R Ω ((divX^[j + 1] f).coeff n)) < 1 := by
      have := hfc (n + (j + 1))
      rw [← coeff_iterate_divX] at this
      exact (congrArg 𝒪.valuation this).trans_lt (hgt _ (by omega))
    exact mul_lt_one_of_lt_of_le h1 (pow_le_one' ((𝒪.valuation_le_one_iff y).2 hy) n)
  refine ⟨aeval y (divX^[j] f), isIntegral_aeval_iterate_divX hf j, ?_,
    isIntegral_mul_aeval_iterate_divX hf j (isIntegral_aeval_iterate_divX hf j), fun σ hσ ↦ ?_⟩
  · have hlt : 𝒪.valuation (aeval y (divX^[j + 1] f) * y) < 𝒪.valuation (h.coeff j) := by
      rw [map_mul, hj]
      exact mul_lt_one_of_lt_of_le hw ((𝒪.valuation_le_one_iff y).2 hy)
    rw [hs, add_comm, Valuation.map_add_eq_of_lt_left _ hlt, hj]
  · let φ : Ω →ₐ[R] Ω :=
      { σ.toRingHom with commutes' := fun r ↦ σ.commutes ⟨r, (Subring.mem_inf.1 r.2).2⟩ }
    have hφ : φ y = y := hσ
    exact (aeval_algHom_apply φ y _).symm.trans (congrArg (fun z ↦ aeval z (divX^[j] f)) hφ)


/-- Automorphisms of `Ω` over `F` preserve integrality over subrings of `F`. -/
lemma isIntegral_algEquiv_apply {F : Subfield Ω} {R : Subring Ω} (hR : R ≤ F.toSubring)
    (σ : Ω ≃ₐ[F] Ω) {b : Ω} (hb : IsIntegral R b) : IsIntegral R (σ b) :=
  hb.map ({ σ.toRingHom with commutes' := fun r ↦ σ.commutes ⟨r, hR r.2⟩ } : Ω →ₐ[R] Ω)

/-- An automorphism of `Ω / F` (algebraic) mapping integral units (over `𝒪 ∩ F`) of `𝒪` to
units of `𝒪` maps `𝒪` into itself. -/
lemma apply_mem_of_forall_isIntegral (F : Subfield Ω) [Algebra.IsAlgebraic F Ω]
    (τ : Ω ≃ₐ[F] Ω) (hτ : ∀ b : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b →
      𝒪.valuation b = 1 → 𝒪.valuation (τ b) = 1) {y : Ω} (hy : y ∈ 𝒪) : τ y ∈ 𝒪 := by
  obtain ⟨s, hs, hvs, ht⟩ :=
    exists_isIntegral_mul_isIntegral F hy (Algebra.IsAlgebraic.isAlgebraic y)
  have h := mem_of_isIntegral_of_le inf_le_left (isIntegral_algEquiv_apply inf_le_right τ ht)
  rw [← valuation_le_one_iff, map_mul, map_mul, hτ s hs hvs, mul_one] at h
  rwa [← valuation_le_one_iff]

/-- **Decomposition group = stabiliser of the centre.** If `Ω / F` is algebraic and an
automorphism `σ` of `Ω / F` preserves the centre of `𝒪` on the integral closure of `𝒪 ∩ F`
(i.e. the integral elements of value `< 1`), then `σ` lies in the decomposition group of `𝒪`. -/
theorem mem_decompositionSubgroup_of_forall_isIntegral (F : Subfield Ω)
    [Algebra.IsAlgebraic F Ω] (σ : Ω ≃ₐ[F] Ω)
    (hσ : ∀ b : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b →
      (𝒪.valuation (σ b) < 1 ↔ 𝒪.valuation b < 1)) :
    σ ∈ 𝒪.decompositionSubgroup F := by
  have hle (b : Ω) (hb : IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b) : 𝒪.valuation b ≤ 1 :=
    (valuation_le_one_iff _ _).2 (mem_of_isIntegral_of_le inf_le_left hb)
  have h1 (b : Ω) (hb : IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b) (hb1 : 𝒪.valuation b = 1) :
      𝒪.valuation (σ b) = 1 :=
    le_antisymm (hle _ (isIntegral_algEquiv_apply inf_le_right σ hb)) (not_lt.1 fun h ↦
      (hb1 ▸ ((hσ b hb).1 h)).false)
  have h2 (b : Ω) (hb : IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b) (hb1 : 𝒪.valuation b = 1) :
      𝒪.valuation (σ⁻¹ b) = 1 := by
    have hb' := isIntegral_algEquiv_apply inf_le_right σ⁻¹ hb
    have := hσ _ hb'
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply, hb1] at this
    rw [AlgEquiv.aut_inv] at hb' ⊢
    exact le_antisymm (hle _ hb') (not_lt.1 fun h ↦ (this.2 h).false)
  rw [MulAction.mem_stabilizer_iff]
  ext y
  rw [mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  refine ⟨fun hy ↦ ?_, apply_mem_of_forall_isIntegral F _ h2⟩
  have := apply_mem_of_forall_isIntegral F σ h1 hy
  rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this

/-- Elements of the decomposition group fix residues whose `p`-th powers are residues of `F`:
if `z ^ p ≡ w` with `w ∈ F`, then `σ z ≡ z` for every `σ` in the decomposition group. -/
theorem valuation_apply_sub_lt_one_of_pow_sub {p : ℕ} [Fact p.Prime] [CharP (ResidueField 𝒪) p]
    {F : Subfield Ω} (σ : 𝒪.decompositionSubgroup F) {z w : Ω} (hz : z ∈ 𝒪) (hw : w ∈ F)
    (hzw : 𝒪.valuation (z ^ p - w) < 1) :
    𝒪.valuation ((σ : Ω ≃ₐ[F] Ω) z - z) < 1 := by
  refine valuation_sub_lt_one_of_pow 𝒪 p (decompositionSubgroup_apply_mem 𝒪 σ hz) hz ?_
  have hσw : (σ : Ω ≃ₐ[F] Ω) w = w := (σ : Ω ≃ₐ[F] Ω).commutes ⟨w, hw⟩
  have h1 : 𝒪.valuation ((σ : Ω ≃ₐ[F] Ω) (z ^ p - w)) < 1 :=
    valuation_apply_lt_one 𝒪 (σ : Ω ≃ₐ[F] Ω).toRingEquiv
      (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ hx)
      (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ⁻¹ hx) hzw
  have h2 := Valuation.map_sub_lt _ h1 hzw
  rwa [map_sub (σ : Ω ≃ₐ[F] Ω), map_pow (σ : Ω ≃ₐ[F] Ω), hσw, sub_sub_sub_cancel_right] at h2

/-- For `σ ∈ Gal(Ω/F)`, the ring map `b ↦ σ b` from the integral closure of `𝒪 ∩ F` in `Ω`
to `𝒪`. -/
def integralClosureToValuationSubring (F : Subfield Ω) (σ : Ω ≃ₐ[F] Ω) :
    integralClosure ↥(𝒪.toSubring ⊓ F.toSubring) Ω →+* 𝒪 where
  toFun b := ⟨σ b, mem_of_isIntegral_of_le inf_le_left
    (isIntegral_algEquiv_apply inf_le_right σ b.2)⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' _ _ := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' _ _ := Subtype.ext (map_add σ _ _)

/-- **Separation by integral elements.** Let `a` be fixed by the decomposition group of `𝒪` over
`F` and `τ ∈ Gal(Ω/F)` with `τ a ≠ a`. Then some `e`, integral over `𝒪 ∩ F` and fixed by every
automorphism fixing `a`, is a unit of `𝒪` with `τ e` in the maximal ideal. -/
theorem exists_isIntegral_valuation_apply_lt_one [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω] {a : Ω}
    (hfix : ∀ σ : 𝒪.decompositionSubgroup F, (σ : Ω ≃ₐ[F] Ω) a = a) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ a ≠ a) :
    ∃ e : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) e ∧
      (∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ e = e) ∧ 𝒪.valuation e = 1 ∧ 𝒪.valuation (τ e) < 1 := by
  by_contra! h
  set R := 𝒪.toSubring ⊓ F.toSubring
  let Q (σ : Ω ≃ₐ[F] Ω) : Ideal (integralClosure R Ω) :=
    (maximalIdeal 𝒪).comap (integralClosureToValuationSubring F σ)
  have hQ (σ : Ω ≃ₐ[F] Ω) (b : integralClosure R Ω) : b ∈ Q σ ↔ 𝒪.valuation (σ b) < 1 := by
    rw [Ideal.mem_comap, valuation_lt_one_iff]
    rfl
  have hle (b : integralClosure R Ω) : 𝒪.valuation (b : Ω) ≤ 1 :=
    (valuation_le_one_iff _ _).2 (mem_of_isIntegral_of_le inf_le_left b.2)
  have hmax : (Q τ).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (Q τ)
      (Ideal.isMaximal_iff.2 ⟨?_, ?_⟩)
    · rw [Ideal.mem_comap, hQ]
      simp
    · intro J x hle' hx hxJ
      rw [Ideal.mem_comap, hQ] at hx
      have hτx : τ (x : Ω) = x := τ.commutes ⟨x, (Subring.mem_inf.1 x.2).2⟩
      have hx1 : 𝒪.valuation (x : Ω) = 1 := by
        refine le_antisymm ((valuation_le_one_iff _ _).2 (Subring.mem_inf.1 x.2).1) ?_
        rw [← hτx]
        exact not_lt.1 hx
      have hx0 : (x : Ω) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hx1
        exact zero_ne_one hx1
      have hxinv : (x : Ω)⁻¹ ∈ R := Subring.mem_inf.2
        ⟨(valuation_le_one_iff _ _).1 (by rw [map_inv₀, hx1, inv_one]),
          F.inv_mem (Subring.mem_inf.1 x.2).2⟩
      have h1 : (1 : R) = ⟨_, hxinv⟩ * x := Subtype.ext (inv_mul_cancel₀ hx0).symm
      rw [h1]
      exact J.mul_mem_left _ hxJ
  obtain ⟨g, hga, hg⟩ := exists_smul_of_under_eq_of_stabilizer inf_le_right a (Q τ) (Q 1)
    fun b hb hbQ ↦ by
      rw [hQ] at hbQ ⊢
      rw [AlgEquiv.one_apply]
      by_contra hb1
      exact (h b b.2 hb (le_antisymm (hle b) (not_lt.1 hb1))).not_gt hbQ
  have hD : τ * g⁻¹ ∈ 𝒪.decompositionSubgroup F := by
    refine mem_decompositionSubgroup_of_forall_isIntegral F _ fun b hb ↦ ?_
    have := hg ⟨b, hb⟩
    rw [hQ, hQ, AlgEquiv.one_apply] at this
    exact this.symm
  have hga' : g⁻¹ a = a := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hga]
  have := hfix ⟨_, hD⟩
  rw [AlgEquiv.mul_apply, hga'] at this
  exact hτ this

/-- **(HZ) The decomposition field has the residue field of `F`** (residue part of "the
decomposition field is an immediate extension"). Missing classical input for (R2)/(R3).

Proof sketch (elementary, via the lemmas above): let `E = F(a)`, `B` the integral closure of
`R = 𝒪 ∩ F` in `Ω`, `Q = 𝔪 ∩ B`.
1. (separation) If `τ ∈ Gal(Ω/F)` and `τ a ≠ a`, there is `e ∈ E ∩ B` with `v e = 1`,
   `v (τ e) < 1`: otherwise `τ⁻¹Q ∩ E ⊆ Q ∩ E`, hence equal (both maximal over `𝔪_R`), so by
   transitivity of `Gal(Ω/E)` on primes over `Q ∩ E` (`exists_smul_of_under_eq_of_profinite`)
   some `τρ`, `ρ ∈ Gal(Ω/E)`, stabilises `Q`, so lies in `D`
   (`mem_decompositionSubgroup_of_forall_isIntegral`) and `τ a = τ ρ a = a`.
2. Take `e` the product over the finitely many conjugates `τ a ≠ a`; write `a = t / s`
   (`exists_isIntegral_mul_isIntegral`). Then `Tr_{E/F}(t e) ≡ t e` and `Tr_{E/F}(s e) ≡ s e`
   lie in `𝒪 ∩ F`, so `ā = (Tr(t e))‾ / (Tr(s e))‾` is a residue of `F`. -/
theorem exists_valuation_sub_lt_one_of_forall_decompositionSubgroup [IsSepClosed Ω]
    (F : Subfield Ω) [Algebra.IsSeparable F Ω] {a : Ω} (ha : a ∈ 𝒪)
    (hfix : ∀ σ : 𝒪.decompositionSubgroup F, (σ : Ω ≃ₐ[F] Ω) a = a) :
    ∃ b ∈ F, b ∈ 𝒪 ∧ 𝒪.valuation (a - b) < 1 := by
  classical
  set R := 𝒪.toSubring ⊓ F.toSubring
  have hle (σ : Ω ≃ₐ[F] Ω) {b : Ω} (hb : IsIntegral R b) : 𝒪.valuation (σ b) ≤ 1 :=
    (valuation_le_one_iff _ _).2
      (mem_of_isIntegral_of_le inf_le_left (isIntegral_algEquiv_apply inf_le_right σ hb))
  -- separating elements for the conjugates `c ≠ a` of `a`
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
  set e := ∏ c ∈ S, E c with he
  have hei : IsIntegral R e := prod_mem (S := integralClosure R Ω) fun c _ ↦ hEi c
  have hef (σ : Ω ≃ₐ[F] Ω) (hσ : σ a = a) : σ e = e := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun c _ ↦ hEf c σ hσ
  have hev : 𝒪.valuation e = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun c _ ↦ hEv c
  have hel (σ : Ω ≃ₐ[F] Ω) (hσ : σ a ≠ a) : 𝒪.valuation (σ e) < 1 := by
    have hmem : σ a ∈ S := by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral a), ?_⟩
      rw [← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [he, ← Finset.mul_prod_erase S E hmem, map_mul, map_mul]
    exact mul_lt_one_of_lt_of_le (hEl _ σ rfl hσ)
      (hle σ (prod_mem (S := integralClosure R Ω) fun c _ ↦ hEi c))
  have hconj {y : Ω} (hy : IsIntegral R y) (hyf : ∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ y = y)
      (σ : Ω ≃ₐ[F] Ω) (hσ : σ (y * e) ≠ y * e) : 𝒪.valuation (σ (y * e)) < 1 := by
    have hσa : σ a ≠ a := fun h ↦ hσ (by rw [map_mul, hyf σ h, hef σ h])
    rw [map_mul, map_mul, mul_comm]
    exact mul_lt_one_of_lt_of_le (hel σ hσa) (hle σ hy)
  -- `a = (a s) / s` with `s`, `a s` integral and fixed by the automorphisms fixing `a`
  obtain ⟨s, hsi, hsv, hasi, hsf⟩ := exists_isIntegral_mul_isIntegral_of_forall_apply_eq F ha
    (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨c₁, hc₁F, hc₁i, hc₁⟩ := exists_mem_isIntegral_valuation_sub_lt_one inf_le_right
    𝒪.valuation (hasi.mul hei)
    (hconj hasi fun σ hσ ↦ by rw [map_mul, hσ, hsf σ hσ])
  obtain ⟨c₂, hc₂F, -, hc₂⟩ := exists_mem_isIntegral_valuation_sub_lt_one inf_le_right
    𝒪.valuation (hsi.mul hei) (hconj hsi hsf)
  have hv2 : 𝒪.valuation (s * e) = 1 := by rw [map_mul, hsv, hev, one_mul]
  have hc₂v : 𝒪.valuation c₂ = 1 := by
    rw [← add_sub_cancel (s * e) c₂, Valuation.map_add_eq_of_lt_left _ (by rwa [hv2]), hv2]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc₂v
    exact zero_ne_one hc₂v
  refine ⟨c₁ / c₂, F.div_mem hc₁F hc₂F, ?_, ?_⟩
  · rw [← valuation_le_one_iff, map_div₀, hc₂v, div_one]
    exact hle 1 hc₁i
  · have hdiff : a - c₁ / c₂ = (a * (c₂ - s * e) - (c₁ - a * s * e)) / c₂ := by
      field_simp
      ring
    have h1 : 𝒪.valuation (a * (c₂ - s * e)) < 1 := by
      rw [map_mul, mul_comm]
      exact mul_lt_one_of_lt_of_le hc₂ ((valuation_le_one_iff _ _).2 ha)
    rw [hdiff, map_div₀, hc₂v, div_one]
    exact Valuation.map_sub_lt _ h1 hc₁

end ValuationSubring
