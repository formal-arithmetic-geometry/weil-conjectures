/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral.ResidueInertia
public import WeilConjectures.RingTheory.Valuation.OhmGeneral.PartialFractionBasis
public import WeilConjectures.RingTheory.Valuation.ArtinSchreierNormalForm

/-!
# Ohm's stability theorem: the Artin–Schreier case for the inertia field

In the setting of `ValuationSubring.not_immediate_of_inertiaField`, in characteristic `p`: let
`Lᵗ` be the inertia field of `𝒪` over `F = K(x)`. If `α ∈ Lᵗ` and `θ ^ p - θ = α` has a root in a
field `L₂ ⊇ Lᵗ` in whose residue field `x̄` is not a `p`-th power, then it has a root in `Lᵗ`.

The proof is the Artin–Schreier normal form `exists_artinSchreier_root_of_approx` over lifts of a
Frobenius-closed residue basis, with Hensel's lemma for the inertia field
(`ValuationSubring.exists_pow_sub_self_eq_of_mem_inertiaField`).
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- `p`-th roots and Artin–Schreier roots of the elements of an algebraically closed subfield. -/
lemma exists_pow_eq_and_pow_sub_self_eq_of_isAlgClosed (p : ℕ) [hp : Fact p.Prime]
    (K : Subfield Ω) [IsAlgClosed K] :
    (∀ c ∈ K, ∃ d ∈ K, d ^ p = c) ∧ (∀ c ∈ K, ∃ d ∈ K, d ^ p - d = c) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (⟨c, hc⟩ : K) (Nat.pos_of_ne_zero hp0)
    exact ⟨d, d.2, congrArg Subtype.val hd⟩
  · have h1 : (Polynomial.X : Polynomial K).degree < (Polynomial.X ^ p : Polynomial K).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast hp.out.one_lt
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.X -
      Polynomial.C (⟨c, hc⟩ : K)) (by
        rw [Polynomial.degree_sub_C (by
          rw [Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
          exact_mod_cast Nat.pos_of_ne_zero hp0),
          Polynomial.degree_sub_eq_left_of_degree_lt h1, Polynomial.degree_X_pow]
        exact_mod_cast hp0)
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hd
    exact ⟨d, d.2, congrArg Subtype.val hd⟩

/-- **The residue hypothesis of the Artin–Schreier normal form from (P3).** Let `w` be a family
such that `x` is residually a polynomial, with `p`-th power coefficients from `L₁`, in every
combination `∑ cᵢ wᵢ` (`cᵢ ∈ K` integral, one of them a unit). If `x̄` is not a `p`-th power in
the residue field of `L₂ ⊇ L₁`, then no such combination is residually a `p`-th power from `L₂`. -/
theorem forall_valuation_lt_one_of_residue_pow {p : ℕ} [hp : Fact p.Prime] [CharP Ω p]
    (K L₁ L₂ : Subfield Ω) (hL : L₁ ≤ L₂) {ι : Type*} (w : ι → Ω) {x : Ω}
    (hP3 : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) → (∀ i ∈ s, 𝒪.valuation (c i) ≤ 1) →
      (∃ i ∈ s, 𝒪.valuation (c i) = 1) →
      ∃ (N : ℕ) (y : ℕ → Ω), (∀ k, y k ∈ L₁ ∧ 𝒪.valuation (y k) ≤ 1) ∧
        𝒪.valuation (x - ∑ k ∈ Finset.range N, y k ^ p * (∑ i ∈ s, c i * w i) ^ k) < 1)
    (hxp : ∀ z ∈ L₂, 𝒪.valuation z ≤ 1 → 𝒪.valuation (x - z ^ p) = 1) :
    ∀ z ∈ L₂, 𝒪.valuation z ≤ 1 → ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      (∀ i ∈ s, 𝒪.valuation (c i) ≤ 1) → 𝒪.valuation (z ^ p - ∑ i ∈ s, c i * w i) < 1 →
        ∀ i ∈ s, 𝒪.valuation (c i) < 1 := by
  intro z hz hz1 s c hcK hc1 hlt i hi
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨N, y, hy, hyv⟩ := hP3 s c hcK hc1 ⟨i, hi, le_antisymm (hc1 i hi) hge⟩
  set v := 𝒪.valuation
  set S := ∑ j ∈ s, c j * w j
  set Z := ∑ k ∈ Finset.range N, y k * z ^ k with hZdef
  have hZL : Z ∈ L₂ := sum_mem fun k _ ↦ L₂.mul_mem (hL (hy k).1) (L₂.pow_mem hz _)
  have hZ1 : v Z ≤ 1 := v.map_sum_le fun k _ ↦ by
    rw [map_mul, map_pow]
    exact mul_le_one' (hy k).2 (pow_le_one' hz1 _)
  have hZp : Z ^ p = ∑ k ∈ Finset.range N, y k ^ p * (z ^ p) ^ k := by
    rw [hZdef, sum_pow_char]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k p]
  have hzp1 : v (z ^ p) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one' hz1 _
  have hS1 : v S ≤ 1 := by
    rw [← sub_sub_cancel (z ^ p) S]
    exact v.map_sub_le hzp1 hlt.le
  have h2 : v (∑ k ∈ Finset.range N, y k ^ p * S ^ k - Z ^ p) < 1 := by
    rw [hZp, ← Finset.sum_sub_distrib]
    refine v.map_sum_lt one_ne_zero fun k _ ↦ ?_
    rw [← mul_sub, map_mul, map_pow]
    refine mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one' (hy k).2 _) zero_le ?_
    refine 𝒪.valuation_pow_sub_pow_lt_one hS1 hzp1 ?_ k
    rw [← v.map_neg, neg_sub]
    exact hlt
  have h3 : v (x - Z ^ p) < 1 := by
    rw [← sub_add_sub_cancel x (∑ k ∈ Finset.range N, y k ^ p * S ^ k) (Z ^ p)]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hyv h2)
  rw [hxp Z hZL hZ1] at h3
  exact lt_irrefl _ h3

end ValuationSubring

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω)

/-- **Ohm stability, Artin–Schreier case, from an approximation.** Let `Lᵗ` be the inertia field
of `𝒪` over `F = K(x)` in characteristic `p`, and `w : ι → Lᵗ` a family of elements of value `1`,
valuation independent over `K` (`hval`), such that `x` is residually a polynomial with `p`-th power
coefficients from `Lᵗ` in every combination `∑ cᵢ wᵢ` with a unit coefficient (`hP3`). Let
`α ∈ Lᵗ` be approximated up to an error of value `≤ 1` by `d₀ + ∑ dⱼ (w j.1) ^ p ^ j.2`
(`dⱼ ∈ K`), and `L₂ ⊇ Lᵗ` a field in whose residue field `x̄` is not a `p`-th power (`hxp`). If
`θ ^ p - θ = α` has a root in `L₂`, then it has a root in `Lᵗ`. -/
theorem exists_artinSchreier_root_of_inertiaField_of_approx [IsSepClosed Ω] {p : ℕ}
    [Fact p.Prime] [CharP Ω p] (K : Subfield Ω) [IsAlgClosed K] (x : Ω)
    {ι : Type*} (w : ι → Ω)
    (hw : ∀ i, w i ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x})))
    (hw1 : ∀ i, 𝒪.valuation (w i) = 1)
    (hval : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
      ∀ i ∈ s, 𝒪.valuation (c i) ≤ 𝒪.valuation (∑ j ∈ s, c j * w j))
    (hP3 : ∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) → (∀ i ∈ s, 𝒪.valuation (c i) ≤ 1) →
      (∃ i ∈ s, 𝒪.valuation (c i) = 1) →
      ∃ (N : ℕ) (y : ℕ → Ω), (∀ k, y k ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x})) ∧
        𝒪.valuation (y k) ≤ 1) ∧
        𝒪.valuation (x - ∑ k ∈ Finset.range N, y k ^ p * (∑ i ∈ s, c i * w i) ^ k) < 1)
    (L₂ : Subfield Ω)
    (hL₂ : (𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x}))).toSubfield ≤ L₂)
    (hxp : ∀ z ∈ L₂, 𝒪.valuation z ≤ 1 → 𝒪.valuation (x - z ^ p) = 1)
    {α : Ω} (hα : α ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x})))
    (s : Finset (ι × ℕ)) (d : ι × ℕ → Ω) (hd : ∀ j ∈ s, d j ∈ K) {d₀ : Ω} (hd₀ : d₀ ∈ K)
    (happrox : 𝒪.valuation (α - d₀ - ∑ j ∈ s, d j * w j.1 ^ p ^ j.2) ≤ 1)
    (h₂ : ∃ θ ∈ L₂, θ ^ p - θ = α) :
    ∃ θ ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x})), θ ^ p - θ = α := by
  set L := 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {x}))
  have hKL : K ≤ L.toSubfield := fun c hc ↦
    L.algebraMap_mem ⟨c, Subfield.subset_closure (Or.inl hc)⟩
  obtain ⟨hroot, hAS⟩ := exists_pow_eq_and_pow_sub_self_eq_of_isAlgClosed p K
  exact exists_artinSchreier_root_of_approx p 𝒪.valuation K L.toSubfield L₂ w hKL hL₂ hroot hAS
    hw hw1 hval (fun b hb hb1 ↦ 𝒪.exists_pow_sub_self_eq_of_mem_inertiaField p hb hb1)
    (𝒪.forall_valuation_lt_one_of_residue_pow K L.toSubfield L₂ hL₂ w hP3 hxp) hα s d hd hd₀
    happrox h₂

end ValuationSubring
