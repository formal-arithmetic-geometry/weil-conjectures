/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Approximation by partial fractions in a residually transcendental simple extension

Let `𝒪` be a valuation subring of a field `Ω`, `K ⊆ Ω` an algebraically closed subfield and
`x ∈ 𝒪` whose residue is transcendental over the residue field `k` of `K`. Let `R ⊆ K ∩ 𝒪` be a
set meeting every residue class of `K ∩ 𝒪` (e.g. a set of representatives of `k`,
`ValuationSubring.exists_residue_representatives`). Assuming that the value group of `K` is
"archimedean relative to `Ω`" (every value `< 1` of `K` has powers below any given value), every
element of `K(x)` is approximated to arbitrary precision by `K`-linear combinations of the
monomials `xⁱ` (`i ≥ 0`) and `(x - a)⁻ⁱ` (`i ≥ 1`, `a ∈ R`)
(`ValuationSubring.exists_sub_mem_span_approxMonomials_lt`).

The proof does not need partial fractions explicitly: the span of the monomials is a subalgebra
(`ValuationSubring.mul_mem_span_approxMonomials`), the approximable elements form a subalgebra
(`Valuation.approxClosure`), and each `(x - a)⁻¹`, `a ∈ K`, is approximable by geometric expansion
(`ValuationSubring.inv_sub_mem_approxClosure`); since `K` is algebraically closed, every
denominator splits into such linear factors.
-/

@[expose] public section

open IsLocalRing Polynomial

/-- **Geometric expansion** of `(y - δ)⁻¹` around `y⁻¹`, with exact remainder. -/
lemma inv_sub_eq_sum_add {F : Type*} [Field F] {y : F} (δ : F) (hy : y ≠ 0) (hyδ : y - δ ≠ 0)
    (N : ℕ) : (y - δ)⁻¹ =
      ∑ j ∈ Finset.range N, δ ^ j * y⁻¹ ^ (j + 1) + (δ * y⁻¹) ^ N * (y - δ)⁻¹ := by
  have h := mul_neg_geom_sum (δ * y⁻¹) N
  have hs : ∑ j ∈ Finset.range N, δ ^ j * y⁻¹ ^ (j + 1) =
      y⁻¹ * ∑ j ∈ Finset.range N, (δ * y⁻¹) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h' : (δ * y⁻¹) ^ N = 1 - (1 - δ * y⁻¹) * ∑ j ∈ Finset.range N, (δ * y⁻¹) ^ j := by
    rw [h]
    ring
  rw [hs, h']
  field_simp
  ring

namespace Valuation

variable {Ω Γ₀ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)
  {K : Type*} [Field K] [Algebra K Ω]

/-- The elements of `Ω` approximable to arbitrary precision (for `v`) by elements of `B`. They
form a subalgebra. -/
def approxClosure (B : Subalgebra K Ω) : Subalgebra K Ω where
  carrier := {α | ∀ t : Ω, t ≠ 0 → ∃ S ∈ B, v (α - S) < v t}
  mul_mem' {α β} hα hβ t ht := by
    by_cases h0 : α = 0 ∨ β = 0
    · refine ⟨0, B.zero_mem, ?_⟩
      rcases h0 with rfl | rfl <;> simpa [pos_iff_ne_zero] using ht
    push Not at h0
    obtain ⟨hα0, hβ0⟩ := h0
    obtain ⟨S, hS, hSα⟩ := hα (t * β⁻¹) (by simp [ht, hβ0])
    obtain ⟨T, hT, hTβ⟩ := hβ (if v β ≤ v (t * α⁻¹) then β else t * α⁻¹)
      (by split_ifs <;> simp [*])
    have h1 : v (β - T) < v β := by
      split_ifs at hTβ with h
      exacts [hTβ, hTβ.trans (not_le.1 h)]
    have h2 : v (β - T) < v (t * α⁻¹) := by
      split_ifs at hTβ with h
      exacts [hTβ.trans_le h, hTβ]
    have hvT : v T = v β := by
      have := v.map_sub_eq_of_lt_right h1
      rwa [sub_sub_cancel_left, map_neg] at this
    refine ⟨S * T, B.mul_mem hS hT, ?_⟩
    have hid : α * β - S * T = (α - S) * T + α * (β - T) := by ring
    rw [hid]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul, hvT, ← lt_mul_inv_iff₀ (by simpa [pos_iff_ne_zero] using hβ0), ← map_inv₀,
        ← map_mul]
      exact hSα
    · rw [map_mul, mul_comm, ← lt_mul_inv_iff₀ (by simpa [pos_iff_ne_zero] using hα0), ← map_inv₀,
        ← map_mul]
      exact h2
  add_mem' {α β} hα hβ t ht := by
    obtain ⟨S, hS, hSα⟩ := hα t ht
    obtain ⟨T, hT, hTβ⟩ := hβ t ht
    refine ⟨S + T, B.add_mem hS hT, ?_⟩
    rw [add_sub_add_comm]
    exact v.map_add_lt hSα hTβ
  algebraMap_mem' c t ht := ⟨algebraMap K Ω c, B.algebraMap_mem c, by
    simpa [pos_iff_ne_zero] using ht⟩

lemma mem_approxClosure {B : Subalgebra K Ω} {α : Ω} :
    α ∈ v.approxClosure B ↔ ∀ t : Ω, t ≠ 0 → ∃ S ∈ B, v (α - S) < v t :=
  Iff.rfl

end Valuation

namespace ValuationSubring

section Monomials

variable {Ω : Type*} [Field Ω] {K : Subfield Ω}

/-- The monomials `xⁱ` (`i ≥ 0`) and `(x - a)⁻ⁱ` (`i ≥ 1`, `a ∈ R`). -/
def approxMonomials (x : Ω) (R : Set Ω) : Set Ω :=
  Set.range (x ^ ·) ∪ ⋃ a ∈ R, Set.range fun i : ℕ ↦ (x - a)⁻¹ ^ (i + 1)

lemma pow_mem_approxMonomials (x : Ω) (R : Set Ω) (i : ℕ) : x ^ i ∈ approxMonomials x R :=
  Or.inl ⟨i, rfl⟩

lemma inv_sub_pow_mem_approxMonomials {x a : Ω} {R : Set Ω} (ha : a ∈ R) (i : ℕ) :
    (x - a)⁻¹ ^ (i + 1) ∈ approxMonomials x R :=
  Or.inr (Set.mem_biUnion ha ⟨i, rfl⟩)

/-- `xⁱ (x - a)⁻ʲ` lies in the span of the monomials. -/
lemma pow_mul_inv_sub_pow_mem_span {x a : Ω} {R : Set Ω} (ha : a ∈ R) (haK : a ∈ K)
    (hxa : x - a ≠ 0) (i j : ℕ) :
    x ^ i * (x - a)⁻¹ ^ j ∈ Submodule.span K (approxMonomials x R) := by
  induction i generalizing j with
  | zero =>
    rcases j with _ | j
    · simpa using Submodule.subset_span (pow_mem_approxMonomials x R 0)
    · simpa using Submodule.subset_span (R := K) (inv_sub_pow_mem_approxMonomials (x := x) ha j)
  | succ i ih =>
    rcases j with _ | j
    · simpa using Submodule.subset_span (R := K) (pow_mem_approxMonomials x R (i + 1))
    · have hid : x ^ (i + 1) * (x - a)⁻¹ ^ (j + 1) =
          x ^ i * (x - a)⁻¹ ^ j + (⟨a, haK⟩ : K) • (x ^ i * (x - a)⁻¹ ^ (j + 1)) := by
        rw [Subfield.smul_def]
        linear_combination (x ^ i * (x - a)⁻¹ ^ j) * mul_inv_cancel₀ hxa
      rw [hid]
      exact Submodule.add_mem _ (ih j) (Submodule.smul_mem _ _ (ih (j + 1)))

/-- `(x - a)⁻ⁱ (x - b)⁻ʲ` lies in the span of the monomials. -/
lemma inv_sub_pow_mul_inv_sub_pow_mem_span {x a b : Ω} {R : Set Ω} (ha : a ∈ R) (hb : b ∈ R)
    (haK : a ∈ K) (hbK : b ∈ K) (hxa : x - a ≠ 0) (hxb : x - b ≠ 0) (i j : ℕ) :
    (x - a)⁻¹ ^ i * (x - b)⁻¹ ^ j ∈ Submodule.span K (approxMonomials x R) := by
  by_cases hab : a = b
  · subst hab
    rw [← pow_add]
    simpa using pow_mul_inv_sub_pow_mem_span ha haK hxa 0 (i + j)
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  induction i generalizing j with
  | zero => simpa using pow_mul_inv_sub_pow_mem_span hb hbK hxb 0 j
  | succ i ih =>
    induction j with
    | zero => simpa using pow_mul_inv_sub_pow_mem_span ha haK hxa 0 (i + 1)
    | succ j ihj =>
      have hid : (x - a)⁻¹ ^ (i + 1) * (x - b)⁻¹ ^ (j + 1) =
          (⟨(a - b)⁻¹, K.inv_mem (K.sub_mem haK hbK)⟩ : K) •
            ((x - a)⁻¹ ^ (i + 1) * (x - b)⁻¹ ^ j - (x - a)⁻¹ ^ i * (x - b)⁻¹ ^ (j + 1)) := by
        rw [Subfield.smul_def]
        linear_combination (-((x - a)⁻¹ ^ (i + 1) * (x - b)⁻¹ ^ (j + 1))) * mul_inv_cancel₀ hab' +
          ((a - b)⁻¹ * (x - a)⁻¹ ^ (i + 1) * (x - b)⁻¹ ^ j) * mul_inv_cancel₀ hxb -
          ((a - b)⁻¹ * (x - a)⁻¹ ^ i * (x - b)⁻¹ ^ (j + 1)) * mul_inv_cancel₀ hxa
      rw [hid]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ ihj (ih (j + 1)))

/-- The span of the monomials is closed under multiplication. -/
lemma mul_mem_span_approxMonomials {x : Ω} {R : Set Ω} (hRK : R ⊆ K)
    (hxR : ∀ a ∈ R, x - a ≠ 0) {y z : Ω} (hy : y ∈ Submodule.span K (approxMonomials x R))
    (hz : z ∈ Submodule.span K (approxMonomials x R)) :
    y * z ∈ Submodule.span K (approxMonomials x R) := by
  have h := Submodule.mul_mem_mul hy hz
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  rcases hp with ⟨i, rfl⟩ | hp <;> rcases hq with ⟨j, rfl⟩ | hq
  all_goals dsimp only
  · rw [← pow_add]
    exact Submodule.subset_span (pow_mem_approxMonomials x R _)
  · obtain ⟨b, hb, j, rfl⟩ := Set.mem_iUnion₂.1 hq
    exact pow_mul_inv_sub_pow_mem_span hb (hRK hb) (hxR b hb) i (j + 1)
  · obtain ⟨a, ha, i, rfl⟩ := Set.mem_iUnion₂.1 hp
    rw [mul_comm]
    exact pow_mul_inv_sub_pow_mem_span ha (hRK ha) (hxR a ha) j (i + 1)
  · obtain ⟨a, ha, i, rfl⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨b, hb, j, rfl⟩ := Set.mem_iUnion₂.1 hq
    exact inv_sub_pow_mul_inv_sub_pow_mem_span ha hb (hRK ha) (hRK hb) (hxR a ha) (hxR b hb) _ _

/-- The span of the monomials, as a subalgebra. -/
def approxMonomialsSubalgebra {x : Ω} {R : Set Ω} (hRK : R ⊆ K) (hxR : ∀ a ∈ R, x - a ≠ 0) :
    Subalgebra K Ω :=
  (Submodule.span K (approxMonomials x R)).toSubalgebra
    (by simpa using Submodule.subset_span (R := K) (pow_mem_approxMonomials x R 0))
    fun _ _ ↦ mul_mem_span_approxMonomials hRK hxR

lemma mem_approxMonomialsSubalgebra {x : Ω} {R : Set Ω} (hRK : R ⊆ K) (hxR : ∀ a ∈ R, x - a ≠ 0)
    {y : Ω} : y ∈ approxMonomialsSubalgebra hRK hxR ↔ y ∈ Submodule.span K (approxMonomials x R) :=
  Submodule.mem_toSubalgebra

end Monomials

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- If the residue of `x ∈ 𝒪` is transcendental over the residues of `K`, then `v (x - a) = 1`
for every integral `a ∈ K`. -/
lemma valuation_sub_eq_one {K : Subfield Ω} {x : 𝒪}
    (hx : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) {a : Ω} (haK : a ∈ K)
    (ha : 𝒪.valuation a ≤ 1) : 𝒪.valuation ((x : Ω) - a) = 1 := by
  set a' : 𝒪 := ⟨a, (𝒪.valuation_le_one_iff _).1 ha⟩
  have hsub : ((x - a' : 𝒪) : Ω) = x - a := rfl
  rw [← hsub, ← valuation_eq_one_iff, ← residue_ne_zero_iff_isUnit, map_sub, sub_ne_zero]
  intro h
  refine hx ?_
  rw [h]
  exact isAlgebraic_algebraMap (⟨_, residue_mem_residueSubfield haK⟩ : 𝒪.residueSubfield K)

/-- A set of representatives in `K ∩ 𝒪` of the residues of `K`: it meets every residue class of
`K ∩ 𝒪` exactly once. -/
theorem exists_residue_representatives (K : Subfield Ω) :
    ∃ R : Set Ω, R ⊆ K ∧ (∀ a ∈ R, 𝒪.valuation a ≤ 1) ∧
      (∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1) ∧
      ∀ a ∈ R, ∀ b ∈ R, 𝒪.valuation (a - b) < 1 → a = b := by
  choose σ hσK hσ using fun z : 𝒪.residueSubfield K ↦ mem_residueSubfield.1 z.2
  refine ⟨Set.range fun z ↦ (σ z : Ω), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hσK z
  · rintro _ ⟨z, rfl⟩
    exact 𝒪.valuation_le_one _
  · intro a haK ha
    set a' : 𝒪 := ⟨a, (𝒪.valuation_le_one_iff _).1 ha⟩
    refine ⟨_, ⟨⟨residue 𝒪 a', residue_mem_residueSubfield haK⟩, rfl⟩, ?_⟩
    have hsub : ((a' - σ ⟨residue 𝒪 a', residue_mem_residueSubfield haK⟩ : 𝒪) : Ω) =
        a - σ ⟨residue 𝒪 a', residue_mem_residueSubfield haK⟩ := rfl
    rw [← hsub, ← valuation_lt_one_iff, ← residue_eq_zero_iff, map_sub, hσ, sub_self]
  · rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩ h
    have h' : 𝒪.valuation ((σ z - σ z' : 𝒪) : Ω) < 1 := h
    rw [← valuation_lt_one_iff, ← residue_eq_zero_iff, map_sub, hσ, hσ, sub_eq_zero] at h'
    rw [Subtype.ext h']

/-- Each `(x - a)⁻¹`, `a ∈ K`, is approximable by any subalgebra containing `x` and the
`(x - a₀)⁻¹`, `a₀ ∈ R`: by geometric expansion around `x - a₀` (`a` integral, `a₀ ≡ a`) or around
`-a` (`v a > 1`). -/
theorem inv_sub_mem_approxClosure {K : Subfield Ω} {x : 𝒪}
    (hx : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {R : Set Ω} (hRK : R ⊆ K)
    (hR : ∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1)
    (B : Subalgebra K Ω) (hxB : (x : Ω) ∈ B) (hRB : ∀ a ∈ R, ((x : Ω) - a)⁻¹ ∈ B)
    {a : Ω} (haK : a ∈ K) : ((x : Ω) - a)⁻¹ ∈ 𝒪.valuation.approxClosure B := by
  intro t ht
  have hK {c : Ω} (hc : c ∈ K) : c ∈ B := B.algebraMap_mem ⟨c, hc⟩
  rcases le_or_gt (𝒪.valuation a) 1 with ha | ha
  · obtain ⟨a₀, ha₀R, hδ⟩ := hR a haK ha
    have ha₀K := hRK ha₀R
    have ha₀ : 𝒪.valuation a₀ ≤ 1 := by
      have := 𝒪.valuation.map_sub a (a - a₀)
      rw [sub_sub_cancel] at this
      exact this.trans (max_le ha hδ.le)
    have hy := valuation_sub_eq_one hx ha₀K ha₀
    have hxa := valuation_sub_eq_one hx haK ha
    by_cases hδ0 : a - a₀ = 0
    · refine ⟨((x : Ω) - a₀)⁻¹, hRB a₀ ha₀R, ?_⟩
      rw [sub_eq_zero.1 hδ0]
      simpa [pos_iff_ne_zero] using ht
    obtain ⟨N, hN⟩ := hrk (a - a₀) (K.sub_mem haK ha₀K) t hδ0 ht hδ
    have hid := inv_sub_eq_sum_add (y := (x : Ω) - a₀) (a - a₀)
      (by simp [← 𝒪.valuation.ne_zero_iff, hy])
      (by simp [← 𝒪.valuation.ne_zero_iff, hxa]) N
    rw [sub_sub_sub_cancel_right] at hid
    refine ⟨∑ j ∈ Finset.range N, (a - a₀) ^ j * ((x : Ω) - a₀)⁻¹ ^ (j + 1),
      sum_mem fun j _ ↦ B.mul_mem (pow_mem (hK (K.sub_mem haK ha₀K)) j)
        (pow_mem (hRB a₀ ha₀R) _), ?_⟩
    rw [hid, add_sub_cancel_left]
    simpa [hy, hxa] using hN
  · have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have hxa : 𝒪.valuation ((x : Ω) - a) = 𝒪.valuation a :=
      𝒪.valuation.map_sub_eq_of_lt_right ((𝒪.valuation_le_one x).trans_lt ha)
    obtain ⟨N, hN⟩ := hrk a⁻¹ (K.inv_mem haK) t (inv_ne_zero ha0) ht
      (by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ ha)
    have hid := inv_sub_eq_sum_add (y := -a) (-(x : Ω)) (neg_ne_zero.2 ha0)
      (by rw [neg_sub_neg, ← 𝒪.valuation.ne_zero_iff, hxa]; simpa using ha0) N
    rw [neg_sub_neg] at hid
    refine ⟨∑ j ∈ Finset.range N, (-(x : Ω)) ^ j * (-a)⁻¹ ^ (j + 1),
      sum_mem fun j _ ↦ B.mul_mem (pow_mem (B.neg_mem hxB) j)
        (pow_mem (hK (K.inv_mem (K.neg_mem haK))) _), ?_⟩
    rw [hid, add_sub_cancel_left]
    rw [map_inv₀] at hN
    refine lt_of_le_of_lt ?_ hN
    simp only [map_mul, map_pow, Valuation.map_neg, map_inv₀, hxa]
    calc _ ≤ (𝒪.valuation a)⁻¹ ^ N * 1 :=
          mul_le_mul' (pow_le_pow_left₀ zero_le
            (mul_le_of_le_one_left' (𝒪.valuation_le_one x)) N) (inv_le_one_of_one_le₀ ha.le)
      _ = _ := mul_one _

/-- **Approximation by partial fractions.** Every element of `K(x)` is approximated to arbitrary
precision by `K`-linear combinations of `xⁱ` (`i ≥ 0`) and `(x - a)⁻ⁱ` (`i ≥ 1`, `a ∈ R`). -/
theorem exists_sub_mem_span_approxMonomials_lt {K : Subfield Ω} [IsAlgClosed K] {x : 𝒪}
    (hx : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {R : Set Ω} (hRK : R ⊆ K) (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hR : ∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1)
    {α : Ω} (hα : α ∈ IntermediateField.adjoin K {(x : Ω)}) {t : Ω} (ht : t ≠ 0) :
    ∃ S ∈ Submodule.span K (approxMonomials (x : Ω) R), 𝒪.valuation (α - S) < 𝒪.valuation t := by
  have hxR (a : Ω) (ha : a ∈ R) : (x : Ω) - a ≠ 0 := by
    intro h
    have := valuation_sub_eq_one hx (hRK ha) (hR𝒪 a ha)
    rw [h, map_zero] at this
    exact zero_ne_one this
  set B := approxMonomialsSubalgebra hRK hxR
  have hxB : (x : Ω) ∈ B := (mem_approxMonomialsSubalgebra hRK hxR).2 <| by
    simpa using Submodule.subset_span (R := K) (pow_mem_approxMonomials (x : Ω) R 1)
  have hRB (a : Ω) (ha : a ∈ R) : ((x : Ω) - a)⁻¹ ∈ B :=
    (mem_approxMonomialsSubalgebra hRK hxR).2 <| by
    simpa using Submodule.subset_span (R := K) (inv_sub_pow_mem_approxMonomials (x := (x : Ω)) ha 0)
  set C := 𝒪.valuation.approxClosure B
  suffices hαC : α ∈ C from hαC t ht
  have hxC : (x : Ω) ∈ C := fun t ht ↦ ⟨x, hxB, by simpa [pos_iff_ne_zero] using ht⟩
  have hpoly (p : K[X]) : aeval (x : Ω) p ∈ C :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hxC) (aeval_mem_adjoin_singleton K _)
  obtain ⟨f, g, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K α).1 hα
  rw [div_eq_mul_inv]
  refine C.mul_mem (hpoly f) ?_
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g) IsAlgClosed.card_roots_eq_natDegree,
    map_mul, aeval_C, mul_inv, ← map_inv₀]
  refine C.mul_mem (C.algebraMap_mem _) ?_
  induction g.roots using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_inv]
    refine C.mul_mem ?_ ih
    rw [map_sub, aeval_X, aeval_C]
    exact inv_sub_mem_approxClosure hx hrk hRK hR B hxB hRB a.2

end ValuationSubring
