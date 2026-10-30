/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral.PartialFractions
public import WeilConjectures.RingTheory.Valuation.OhmGeneral.Residue
public import WeilConjectures.FieldTheory.FrobeniusClosedBasisSubfield

/-!
# The partial-fraction basis of a rational function field

For `t` transcendental over a field `k`, the monomials `tᵐ` (`m ≥ 0`) and `(t - a)⁻ⁱ` (`i ≥ 1`,
`a ∈ k`) are linearly independent over `k` (`linearIndependent_partialFractionMonomials`), by the
uniqueness of partial fraction decompositions.
-/

@[expose] public section

open Polynomial

/-- The partial-fraction monomials `tᵐ` (`m ≥ 0`) and `(t - a)⁻⁽ⁱ⁺¹⁾` (`a ∈ k`, `i ≥ 0`). -/
noncomputable def partialFractionMonomial {k E : Type*} [Field k] [Field E] [Algebra k E]
    (t : E) : ℕ ⊕ (k × ℕ) → E :=
  Sum.elim (fun m ↦ t ^ m) fun q ↦ (t - algebraMap k E q.1)⁻¹ ^ (q.2 + 1)

/-- **Uniqueness of partial fractions**: for `t` transcendental over `k`, the monomials `tᵐ`
(`m ≥ 0`) and `(t - a)⁻⁽ⁱ⁺¹⁾` (`a ∈ k`, `i ≥ 0`) are linearly independent over `k`. -/
theorem linearIndependent_partialFractionMonomial {k E : Type*} [Field k] [Field E] [Algebra k E]
    {t : E} (ht : Transcendental k t) :
    LinearIndependent k (partialFractionMonomial (k := k) t) := by
  classical
  let : Algebra k[X] E := (aeval t).toRingHom.toAlgebra
  have halg (f : k[X]) : algebraMap k[X] E f = aeval t f := rfl
  have : FaithfulSMul k[X] E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (transcendental_iff_injective.1 ht)
  rw [linearIndependent_iff']
  intro s g hg j hj
  set s₁ := s.toLeft
  set s₂ := s.toRight
  set T := s₂.image Prod.fst
  set N := s₂.sup Prod.snd + 1
  have hN (q : k × ℕ) (hq : q ∈ s₂) : q.2 < N := Nat.lt_succ_of_le (Finset.le_sup hq)
  set r : k → Fin N → k[X] := fun a j ↦ C (if (a, (j : ℕ)) ∈ s₂ then g (.inr (a, j)) else 0)
  have hr (a : k) (j : Fin N) : (r a j).degree < (X - C a).degree := by
    rw [degree_X_sub_C]
    exact degree_C_le.trans_lt (by norm_num)
  have hsum : algebraMap k[X] E (∑ m ∈ s₁, C (g (.inl m)) * X ^ m) + ∑ a ∈ T, ∑ j : Fin N,
      algebraMap k[X] E (r a j) * (t - algebraMap k E a)⁻¹ ^ ((j : ℕ) + 1) =
      algebraMap k[X] E 0 + ∑ a ∈ T, ∑ j : Fin N,
        algebraMap k[X] E ((fun _ _ ↦ 0 : k → Fin N → k[X]) a j) *
          (t - algebraMap k E a)⁻¹ ^ ((j : ℕ) + 1) := by
    simp only [map_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [← hg, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
    congr 1
    · simp [halg, partialFractionMonomial, Algebra.smul_def, s₁]
    · calc ∑ a ∈ T, ∑ j : Fin N,
          algebraMap k[X] E (r a j) * (t - algebraMap k E a)⁻¹ ^ ((j : ℕ) + 1)
          = ∑ a ∈ T, ∑ j ∈ Finset.range N, if (a, j) ∈ s₂ then
              g (.inr (a, j)) • (t - algebraMap k E a)⁻¹ ^ (j + 1) else 0 := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Fin.sum_univ_eq_sum_range (fun j ↦ if (a, j) ∈ s₂ then
              g (.inr (a, j)) • (t - algebraMap k E a)⁻¹ ^ (j + 1) else 0) N]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            split_ifs <;> simp [r, *, Algebra.smul_def]
        _ = ∑ q ∈ T ×ˢ Finset.range N, if q ∈ s₂ then
              g (.inr q) • (t - algebraMap k E q.1)⁻¹ ^ (q.2 + 1) else 0 :=
            by rw [Finset.sum_product]
        _ = _ := by
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun q _ ↦ ?_
            · ext q
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
              exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨Finset.mem_image_of_mem _ h, hN q h⟩, h⟩⟩
            · simp [partialFractionMonomial]
  have hne (a : k) : t - algebraMap k E a ≠ 0 := fun h ↦
    ht (by rw [sub_eq_zero.1 h]; exact isAlgebraic_algebraMap a)
  obtain ⟨hq, hr0⟩ := quo_add_sum_rem_mul_pow_inverse_unique (K := E) (s := T)
    (g := fun a ↦ X - C a) (fun a _ ↦ monic_X_sub_C a)
    ((pairwise_coprime_X_sub_C (s := id) Function.injective_id).set_pairwise _)
    (n := fun _ ↦ N) (gi := fun a ↦ (t - algebraMap k E a)⁻¹)
    (fun a _ ↦ by rw [halg]; simp [inv_mul_cancel₀ (hne a)]) (fun a _ j ↦ hr a j)
    (fun a _ j ↦ by simp [degree_X_sub_C]) hsum
  rcases j with m | q
  · have h := congrArg (coeff · m) hq
    simpa [finsetSum_coeff, coeff_C_mul_X_pow, s₁, Finset.mem_toLeft.2 hj] using h
  · have hq' : q ∈ s₂ := Finset.mem_toRight.2 hj
    have h := congrFun (hr0 q.1 (Finset.mem_image_of_mem _ hq')) ⟨q.2, hN q hq'⟩
    simpa [r, hq'] using h

namespace ValuationSubring

open IsLocalRing

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- **Valuation independence from residual linear independence.** If the residues of the integral
elements `m j` are linearly independent over the residue field of `K`, then the value of a
`K`-combination `∑ cⱼ mⱼ` is at least the value of each coefficient. -/
theorem valuation_le_valuation_sum_of_linearIndependent {K : Subfield Ω} {J : Type*}
    {m : J → Ω} (hm : ∀ j, m j ∈ 𝒪)
    (hli : LinearIndependent (𝒪.residueSubfield K) fun j ↦ residue 𝒪 ⟨m j, hm j⟩)
    (s : Finset J) (c : J → Ω) (hc : ∀ j ∈ s, c j ∈ K) :
    ∀ j ∈ s, 𝒪.valuation (c j) ≤ 𝒪.valuation (∑ i ∈ s, c i * m i) := by
  classical
  intro j hj
  obtain ⟨j₀, hj₀, hmax⟩ := s.exists_max_image (fun i ↦ 𝒪.valuation (c i)) ⟨j, hj⟩
  refine (hmax j hj).trans ?_
  by_cases h0 : c j₀ = 0
  · simp [h0]
  have hv0 : 𝒪.valuation (c j₀) ≠ 0 := by simpa using h0
  have he (i : J) (hi : i ∈ s) : 𝒪.valuation (c i / c j₀) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (hmax i hi) zero_le
  let E : J → 𝒪 := fun i ↦ if hi : i ∈ s then ⟨c i / c j₀, (𝒪.valuation_le_one_iff _).1 (he i hi)⟩
    else 0
  have hEK (i : J) : (E i : Ω) ∈ K := by
    by_cases hi : i ∈ s
    · simpa [E, hi] using K.div_mem (hc i hi) (hc j₀ hj₀)
    · simp [E, hi]
  have hsum : ∑ i ∈ s, c i * m i = c j₀ * ((∑ i ∈ s, E i * ⟨m i, hm i⟩ : 𝒪) : Ω) := by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [E, hi, dite_true, MulMemClass.coe_mul]
    field_simp
  rw [hsum, map_mul]
  refine le_mul_of_one_le_right' (not_lt.1 fun hlt ↦ ?_)
  rw [← valuation_lt_one_iff, ← residue_eq_zero_iff, map_sum] at hlt
  have h := linearIndependent_iff'.1 hli s
    (fun i ↦ ⟨residue 𝒪 (E i), residue_mem_residueSubfield (hEK i)⟩) (by
      rw [← hlt]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul]
      rfl) j₀ hj₀
  have h1 : E j₀ = 1 := Subtype.ext (by simp [E, hj₀, h0])
  have h' : residue 𝒪 (E j₀) = 0 := congrArg Subtype.val h
  rw [h1, map_one] at h'
  exact one_ne_zero h'


/-- The partial-fraction monomials `xᵐ` (`m ≥ 0`) and `(x - a)⁻⁽ⁱ⁺¹⁾` (`a ∈ R`, `i ≥ 0`) in `Ω`. -/
noncomputable def partialFractionLift (x : Ω) (R : Set Ω) : ℕ ⊕ (R × ℕ) → Ω :=
  Sum.elim (fun m ↦ x ^ m) fun q ↦ (x - q.1)⁻¹ ^ (q.2 + 1)

lemma approxMonomials_eq_range (x : Ω) (R : Set Ω) :
    approxMonomials x R = Set.range (partialFractionLift x R) := by
  ext y
  simp [approxMonomials, partialFractionLift, Set.mem_iUnion]

/-- In Ohm's setting, the partial-fraction monomials have value `1`. -/
lemma valuation_partialFractionLift {K : Subfield Ω} {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) {R : Set Ω} (hRK : R ⊆ K)
    (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1) (j : ℕ ⊕ (R × ℕ)) :
    𝒪.valuation (partialFractionLift (x : Ω) R j) = 1 := by
  rcases j with m | ⟨⟨a, ha⟩, i⟩
  · simp [partialFractionLift, valuation_eq_one_of_transcendental htr]
  · simp [partialFractionLift, valuation_sub_eq_one htr (hRK ha) (hR𝒪 a ha)]

/-- In Ohm's setting, the residues of the partial-fraction monomials, for a set `R` of
representatives of distinct residue classes, are linearly independent over `k`. -/
theorem linearIndependent_residue_partialFractionLift {K : Subfield Ω} {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) {R : Set Ω} (hRK : R ⊆ K)
    (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hRinj : ∀ a ∈ R, ∀ b ∈ R, 𝒪.valuation (a - b) < 1 → a = b) :
    LinearIndependent (𝒪.residueSubfield K) fun j ↦ residue 𝒪
      ⟨partialFractionLift (x : Ω) R j, (𝒪.valuation_le_one_iff _).1
        (valuation_partialFractionLift htr hRK hR𝒪 j).le⟩ := by
  let ρ : R → 𝒪.residueSubfield K := fun a ↦
    ⟨residue 𝒪 ⟨a, (𝒪.valuation_le_one_iff _).1 (hR𝒪 a a.2)⟩, residue_mem_residueSubfield (hRK a.2)⟩
  have hρ : Function.Injective ρ := by
    intro a b hab
    have h : residue 𝒪 ⟨a, (𝒪.valuation_le_one_iff _).1 (hR𝒪 a a.2)⟩ =
        residue 𝒪 ⟨b, (𝒪.valuation_le_one_iff _).1 (hR𝒪 b b.2)⟩ := congrArg Subtype.val hab
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, valuation_lt_one_iff] at h
    exact Subtype.ext (hRinj a a.2 b b.2 h)
  have hφ : Function.Injective (Sum.map (id : ℕ → ℕ) (Prod.map ρ (id : ℕ → ℕ))) := by
    refine Sum.map_injective.2 ⟨Function.injective_id, ?_⟩
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h
    rw [hρ h.1, h.2]
  convert (linearIndependent_partialFractionMonomial htr).comp _ hφ using 1
  · funext j
    rcases j with m | ⟨a, i⟩
    · simp only [Function.comp_apply, Sum.map_inl, id_eq, partialFractionMonomial, Sum.elim_inl]
      rw [← map_pow]
      rfl
    · simp only [Function.comp_apply, Sum.map_inr, Prod.map_apply, id_eq, partialFractionMonomial,
        Sum.elim_inr]
      have hxa : 𝒪.valuation ((x : Ω) - a) = 1 := valuation_sub_eq_one htr (hRK a.2) (hR𝒪 a a.2)
      set u : 𝒪 := ⟨(x : Ω) - a, (𝒪.valuation_le_one_iff _).1 hxa.le⟩
      set u' : 𝒪 := ⟨((x : Ω) - a)⁻¹, (𝒪.valuation_le_one_iff _).1 (by simp [hxa])⟩
      have hu : u' * u = 1 :=
        Subtype.ext (inv_mul_cancel₀ (by simp [← 𝒪.valuation.ne_zero_iff, hxa]))
      have hres : residue 𝒪 u = residue 𝒪 x - algebraMap (𝒪.residueSubfield K) _ (ρ a) := by
        have hu2 : u = x - ⟨(a : Ω), (𝒪.valuation_le_one_iff _).1 (hR𝒪 a a.2)⟩ := rfl
        rw [hu2, map_sub]
        rfl
      have h1 : residue 𝒪 u' = (residue 𝒪 x - algebraMap (𝒪.residueSubfield K) _ (ρ a))⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← hres, ← map_mul, hu, map_one]
      rw [← h1, ← map_pow]
      rfl
  · rfl

/-- **Valuation independence of the partial-fraction monomials** over `K`. -/
theorem valuation_le_valuation_sum_partialFractionLift {K : Subfield Ω} {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x)) {R : Set Ω} (hRK : R ⊆ K)
    (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hRinj : ∀ a ∈ R, ∀ b ∈ R, 𝒪.valuation (a - b) < 1 → a = b)
    (s : Finset (ℕ ⊕ (R × ℕ))) (c : ℕ ⊕ (R × ℕ) → Ω) (hc : ∀ j ∈ s, c j ∈ K) :
    ∀ j ∈ s, 𝒪.valuation (c j) ≤
      𝒪.valuation (∑ i ∈ s, c i * partialFractionLift (x : Ω) R i) :=
  valuation_le_valuation_sum_of_linearIndependent _
    (linearIndependent_residue_partialFractionLift htr hRK hR𝒪 hRinj) s c hc


/-- The base of a partial-fraction monomial: `x` or `(x - a)⁻¹`. -/
noncomputable def partialFractionBase (x : Ω) (R : Set Ω) : ℕ ⊕ (R × ℕ) → Ω :=
  Sum.elim (fun _ ↦ x) fun q ↦ (x - q.1)⁻¹

/-- The exponent of a partial-fraction monomial. -/
def partialFractionExponent (R : Set Ω) : ℕ ⊕ (R × ℕ) → ℕ :=
  Sum.elim id fun q ↦ q.2 + 1

lemma partialFractionLift_eq (x : Ω) (R : Set Ω) (j : ℕ ⊕ (R × ℕ)) :
    partialFractionLift x R j = partialFractionBase x R j ^ partialFractionExponent R j := by
  rcases j with m | q <;> rfl

/-- Every partial-fraction monomial other than `1` is a `p ^ n`-th power of one whose exponent is
prime to `p`. -/
lemma exists_partialFractionLift_eq_pow (x : Ω) (R : Set Ω) {p : ℕ} (hp : p.Prime)
    (j : ℕ ⊕ (R × ℕ)) (hj : j ≠ .inl 0) :
    ∃ (i : ℕ ⊕ (R × ℕ)) (n : ℕ), ¬ p ∣ partialFractionExponent R i ∧
      partialFractionLift x R j = partialFractionLift x R i ^ p ^ n := by
  have he : partialFractionExponent R j ≠ 0 := by
    rcases j with m | q
    · exact fun h ↦ hj (by simp_all [partialFractionExponent])
    · simp [partialFractionExponent]
  obtain ⟨n, i', hi', heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd he p hp.ne_one
  have hi'0 : i' ≠ 0 := by
    rintro rfl
    exact hi' (dvd_zero p)
  let i : ℕ ⊕ (R × ℕ) := Sum.elim (fun _ ↦ .inl i') (fun q ↦ .inr (q.1, i' - 1)) j
  have hbase : partialFractionBase x R i = partialFractionBase x R j := by
    rcases j with m | q <;> rfl
  have hexp : partialFractionExponent R i = i' := by
    rcases j with m | q
    · rfl
    · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi'0)
  refine ⟨i, n, hexp ▸ hi', ?_⟩
  rw [partialFractionLift_eq, partialFractionLift_eq, hbase, hexp, heq, ← pow_mul, mul_comm]

/-- The `p`-th power of a partial-fraction monomial is a partial-fraction monomial. -/
lemma partialFractionLift_pow (x : Ω) (R : Set Ω) {p : ℕ} (hp : p ≠ 0) (j : ℕ ⊕ (R × ℕ)) :
    partialFractionLift x R j ^ p = partialFractionLift x R
      (Sum.map (p * ·) (fun q ↦ (q.1, p * (q.2 + 1) - 1)) j) := by
  rcases j with m | q
  · simp [partialFractionLift, ← pow_mul, mul_comm]
  · simp only [partialFractionLift, Sum.map_inr, Sum.elim_inr, ← pow_mul]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity)), mul_comm]

omit [Field Ω] in
lemma partialFractionExponent_map (R : Set Ω) (p : ℕ) (hp : p ≠ 0) (j : ℕ ⊕ (R × ℕ)) :
    partialFractionExponent R (Sum.map (p * ·) (fun q ↦ (q.1, p * (q.2 + 1) - 1)) j) =
      p * partialFractionExponent R j := by
  rcases j with m | q
  · rfl
  · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))


/-- **Approximation of `K(x)` by the Frobenius-closed partial-fraction basis.** Every element of
`K(x)` is approximated, up to an error of value `< 1`, by `d₀ + ∑ dⱼ (w j.1) ^ p ^ j.2` with
`d₀, dⱼ ∈ K`, where `w` runs over the partial-fraction monomials with exponent prime to `p`. -/
theorem exists_sub_sum_partialFractionLift_lt {K : Subfield Ω} [IsAlgClosed K] {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {R : Set Ω} (hRK : R ⊆ K) (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hR : ∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1)
    {p : ℕ} (hp : p.Prime) {α : Ω} (hα : α ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) :
    ∃ (s : Finset ({j // ¬ p ∣ partialFractionExponent R j} × ℕ))
      (d : {j // ¬ p ∣ partialFractionExponent R j} × ℕ → Ω), (∀ j ∈ s, d j ∈ K) ∧
      ∃ d₀ ∈ K, 𝒪.valuation (α - d₀ - ∑ j ∈ s, d j * partialFractionLift (x : Ω) R j.1.1 ^ p ^ j.2)
        < 1 := by
  classical
  have hα' : α ∈ IntermediateField.adjoin K {(x : Ω)} := by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield]
    convert hα using 3
    exact Subtype.range_coe
  obtain ⟨S, hS, hαS⟩ := exists_sub_mem_span_approxMonomials_lt htr hrk hRK hR𝒪 hR hα'
    one_ne_zero
  rw [map_one] at hαS
  rw [approxMonomials_eq_range, Finsupp.mem_span_range_iff_exists_finsupp] at hS
  obtain ⟨c, rfl⟩ := hS
  have hdec (j : ℕ ⊕ (R × ℕ)) : ∃ o : Option ({j // ¬ p ∣ partialFractionExponent R j} × ℕ),
      partialFractionLift (x : Ω) R j =
        o.elim 1 fun q ↦ partialFractionLift (x : Ω) R q.1.1 ^ p ^ q.2 := by
    by_cases hj : j = .inl 0
    · exact ⟨none, by simp [hj, partialFractionLift]⟩
    · obtain ⟨i, n, hi, h⟩ := exists_partialFractionLift_eq_pow (x : Ω) R hp j hj
      exact ⟨some (⟨i, hi⟩, n), h⟩
  choose dec hdec using hdec
  set e := c.mapDomain dec
  have hsum : c.sum (fun j a ↦ a • partialFractionLift (x : Ω) R j) = (e none : Ω) +
      ∑ q ∈ e.some.support, (e.some q : Ω) * partialFractionLift (x : Ω) R q.1.1 ^ p ^ q.2 := by
    rw [Finsupp.sum_congr (g2 := fun j a ↦ a • (dec j).elim 1
      fun q ↦ partialFractionLift (x : Ω) R q.1.1 ^ p ^ q.2) fun j _ ↦ by rw [hdec j],
      ← Finsupp.sum_mapDomain_index (f := dec) (s := c)
        (h := fun (o : Option ({j // ¬ p ∣ partialFractionExponent R j} × ℕ)) (a : K) ↦
          a • o.elim (1 : Ω)
        fun q ↦ partialFractionLift (x : Ω) R q.1.1 ^ p ^ q.2) (fun _ ↦ zero_smul _ _)
        (fun _ _ _ ↦ add_smul _ _ _), Finsupp.sum_option_index_smul]
    simp [Finsupp.sum, Subfield.smul_def]
    rfl
  refine ⟨e.some.support, fun q ↦ e.some q, fun q _ ↦ (e.some q).2, e none, (e none).2, ?_⟩
  rw [sub_sub, ← hsum]
  exact hαS


/-- Powers of residually congruent integral elements are residually congruent. -/
lemma valuation_pow_sub_pow_lt_one {S T : Ω} (hS : 𝒪.valuation S ≤ 1) (hT : 𝒪.valuation T ≤ 1)
    (hST : 𝒪.valuation (S - T) < 1) (k : ℕ) : 𝒪.valuation (S ^ k - T ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : S ^ (k + 1) - T ^ (k + 1) = S * (S ^ k - T ^ k) + T ^ k * (S - T) := by ring
    rw [h]
    refine lt_of_le_of_lt (𝒪.valuation.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right hS zero_le ih
    · rw [map_mul, map_pow]
      exact mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one' hT _) zero_le hST

/-- In Ohm's setting, the residue field `k(x̄)` of `K(x)` consists of residues of `K(x) ∩ 𝒪`. -/
lemma exists_residue_eq_of_mem_adjoin (K : Subfield Ω) (x : 𝒪) {z : ResidueField 𝒪}
    (hz : z ∈ IntermediateField.adjoin (𝒪.residueSubfield K) {residue 𝒪 x}) :
    ∃ Z : 𝒪, (Z : Ω) ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}) ∧ residue 𝒪 Z = z := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
  refine (Subfield.closure_le (t := 𝒪.residueSubfield (Subfield.closure ((K : Set Ω) ∪
    {(x : Ω)})))).2 ?_ hz
  rintro _ (⟨c, rfl⟩ | h)
  · exact residueSubfield_mono (fun c hc ↦ Subfield.subset_closure (Or.inl hc)) c.2
  · rw [Set.mem_singleton_iff.1 h]
    exact residue_mem_residueSubfield (Subfield.subset_closure (Or.inr rfl))

/-- In Ohm's setting, a `K`-combination of partial-fraction monomials with exponents prime to `p`
and a unit coefficient is not residually a `p`-th power of an element of `K(x)`. -/
theorem residue_pow_ne_sum_partialFractionLift {p : ℕ} [hp : Fact p.Prime] [CharP Ω p]
    {K : Subfield Ω} [IsAlgClosed K] {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {R : Set Ω} (hRK : R ⊆ K) (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hR : ∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1)
    (hRinj : ∀ a ∈ R, ∀ b ∈ R, 𝒪.valuation (a - b) < 1 → a = b)
    (s : Finset {j // ¬ p ∣ partialFractionExponent R j})
    (c : {j // ¬ p ∣ partialFractionExponent R j} → Ω) (hc : ∀ i ∈ s, c i ∈ K)
    {i₀ : {j // ¬ p ∣ partialFractionExponent R j}} (hi₀ : i₀ ∈ s)
    (hi₀1 : 𝒪.valuation (c i₀) = 1) {Z : Ω} (hZ : Z ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))
    (hZ1 : 𝒪.valuation Z ≤ 1) :
    ¬ 𝒪.valuation (∑ i ∈ s, c i * partialFractionLift (x : Ω) R i.1 - Z ^ p) < 1 := by
  classical
  intro hlt
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set L := partialFractionLift (x : Ω) R
  -- the approximation of `Z` by partial fractions
  have hZ' : Z ∈ IntermediateField.adjoin K {(x : Ω)} := by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield]
    convert hZ using 3
    exact Subtype.range_coe
  obtain ⟨T, hT, hZT⟩ := exists_sub_mem_span_approxMonomials_lt htr hrk hRK hR𝒪 hR hZ'
    one_ne_zero
  rw [map_one] at hZT
  rw [approxMonomials_eq_range, Finsupp.mem_span_range_iff_exists_finsupp] at hT
  obtain ⟨t, rfl⟩ := hT
  have hTsum : (t.sum fun j a ↦ a • L j) = ∑ j ∈ t.support, (t j : Ω) * L j := by
    simp [Finsupp.sum, Subfield.smul_def]
  rw [hTsum] at hZT
  set T := ∑ j ∈ t.support, (t j : Ω) * L j
  have hT1 : 𝒪.valuation T ≤ 1 := by
    rw [← sub_sub_cancel Z T]
    exact 𝒪.valuation.map_sub_le hZ1 hZT.le
  have ht1 (j : ℕ ⊕ (R × ℕ)) (hj : j ∈ t.support) : 𝒪.valuation (t j : Ω) ≤ 1 :=
    (valuation_le_valuation_sum_partialFractionLift htr hRK hR𝒪 hRinj t.support
      (fun j ↦ (t j : Ω)) (fun j _ ↦ (t j).2) j hj).trans hT1
  -- the `p`-th power of the approximation
  set π : ℕ ⊕ (R × ℕ) → ℕ ⊕ (R × ℕ) := Sum.map (p * ·) fun q ↦ (q.1, p * (q.2 + 1) - 1)
  have hTp : T ^ p = ∑ j ∈ t.support, (t j : Ω) ^ p * L (π j) := by
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_pow, partialFractionLift_pow _ _ hp0]
  have hZTp : 𝒪.valuation (Z ^ p - T ^ p) < 1 :=
    𝒪.valuation_pow_sub_pow_lt_one hZ1 hT1 hZT p
  -- the combination `∑ cᵢ wᵢ - T ^ p`
  set D : ℕ ⊕ (R × ℕ) →₀ Ω := ∑ i ∈ s, Finsupp.single i.1 (c i) -
    ∑ j ∈ t.support, Finsupp.single (π j) ((t j : Ω) ^ p)
  have hDsum : D.sum (fun j a ↦ a * L j) = ∑ i ∈ s, c i * L i.1 - T ^ p := by
    rw [Finsupp.sum_sub_index (fun _ _ _ ↦ sub_mul _ _ _), ← Finsupp.sum_finsetSum_index
      (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _), ← Finsupp.sum_finsetSum_index
      (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _), hTp]
    simp
  have hDK (j : ℕ ⊕ (R × ℕ)) : D j ∈ K := by
    simp only [D, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
    refine K.sub_mem (sum_mem fun i hi ↦ ?_) (sum_mem fun i _ ↦ ?_)
    · split_ifs
      exacts [hc i hi, K.zero_mem]
    · split_ifs
      exacts [K.pow_mem (t i).2 _, K.zero_mem]
  have hDi₀ : D i₀.1 = c i₀ := by
    have hπ (j : ℕ ⊕ (R × ℕ)) : π j ≠ i₀.1 := by
      intro h
      have : partialFractionExponent R (π j) = p * partialFractionExponent R j :=
        partialFractionExponent_map R p hp0 j
      rw [h] at this
      exact i₀.2 (this ▸ dvd_mul_right p _)
    simp only [D, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, hπ,
      if_false, Finset.sum_const_zero, sub_zero, Subtype.val_inj]
    rw [Finset.sum_ite_eq' s i₀, if_pos hi₀]
  have hle : 𝒪.valuation (D i₀.1) ≤ 𝒪.valuation (D.sum fun j a ↦ a * L j) :=
    valuation_le_valuation_sum_partialFractionLift htr hRK hR𝒪 hRinj D.support D
      (fun j _ ↦ hDK j) i₀.1 (Finsupp.mem_support_iff.2 (by
        rw [hDi₀]
        intro h0
        rw [h0, map_zero] at hi₀1
        exact zero_ne_one hi₀1))
  rw [hDi₀, hi₀1, hDsum] at hle
  have : ∑ i ∈ s, c i * L i.1 - T ^ p = (∑ i ∈ s, c i * L i.1 - Z ^ p) + (Z ^ p - T ^ p) := by
    ring
  rw [this] at hle
  exact (not_le.2 (𝒪.valuation.map_add_lt hlt hZTp)) hle


/-- **(P3) for `K(x)`.** In Ohm's setting, `x` is residually a polynomial, with `p`-th power
coefficients from `K(x) ∩ 𝒪`, in every `K`-combination `S` of partial-fraction monomials with
exponents prime to `p` with integral coefficients, one of them a unit: `S̄` is not a `p`-th power
in `k(x̄)`, so `k(x̄) = k(x̄) ^ p (S̄)`. -/
theorem exists_sub_sum_pow_mul_partialFractionLift_lt {p : ℕ} [hp : Fact p.Prime] [CharP Ω p]
    [CharP (ResidueField 𝒪) p] {K : Subfield Ω} [IsAlgClosed K] {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t)
    {R : Set Ω} (hRK : R ⊆ K) (hR𝒪 : ∀ a ∈ R, 𝒪.valuation a ≤ 1)
    (hR : ∀ a ∈ K, 𝒪.valuation a ≤ 1 → ∃ a₀ ∈ R, 𝒪.valuation (a - a₀) < 1)
    (hRinj : ∀ a ∈ R, ∀ b ∈ R, 𝒪.valuation (a - b) < 1 → a = b)
    (s : Finset {j // ¬ p ∣ partialFractionExponent R j})
    (c : {j // ¬ p ∣ partialFractionExponent R j} → Ω) (hc : ∀ i ∈ s, c i ∈ K)
    (hc1 : ∀ i ∈ s, 𝒪.valuation (c i) ≤ 1) (hunit : ∃ i ∈ s, 𝒪.valuation (c i) = 1) :
    ∃ (N : ℕ) (y : ℕ → Ω), (∀ k, y k ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}) ∧
        𝒪.valuation (y k) ≤ 1) ∧
      𝒪.valuation ((x : Ω) - ∑ k ∈ Finset.range N,
        y k ^ p * (∑ i ∈ s, c i * partialFractionLift (x : Ω) R i.1) ^ k) < 1 := by
  obtain ⟨i₀, hi₀, hi₀1⟩ := hunit
  set F := Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})
  set S := ∑ i ∈ s, c i * partialFractionLift (x : Ω) R i.1
  have hxF : (x : Ω) ∈ F := Subfield.subset_closure (Or.inr rfl)
  have hLF (j : ℕ ⊕ (R × ℕ)) : partialFractionLift (x : Ω) R j ∈ F := by
    rcases j with m | ⟨⟨a, ha⟩, i⟩
    · exact F.pow_mem hxF m
    · exact F.pow_mem (F.inv_mem (F.sub_mem hxF (Subfield.subset_closure (Or.inl (hRK ha))))) _
  have hSF : S ∈ F := sum_mem fun i hi ↦
    F.mul_mem (Subfield.subset_closure (Or.inl (hc i hi))) (hLF i.1)
  have hS1 : 𝒪.valuation S ≤ 1 := 𝒪.valuation.map_sum_le fun i hi ↦ by
    rw [map_mul, valuation_partialFractionLift htr hRK hR𝒪, mul_one]
    exact hc1 i hi
  set Sb : 𝒪 := ⟨S, (𝒪.valuation_le_one_iff _).1 hS1⟩
  have : IsAlgClosed (𝒪.residueSubfield K) := isAlgClosed_residueSubfield K
  set E := (IntermediateField.adjoin (𝒪.residueSubfield K) {residue 𝒪 x}).toSubfield
  have hρ (z : ResidueField 𝒪) (hz : z ∈ E) : z ^ p ≠ residue 𝒪 Sb := by
    intro hzp
    obtain ⟨Z, hZF, rfl⟩ := exists_residue_eq_of_mem_adjoin K x hz
    refine residue_pow_ne_sum_partialFractionLift htr hrk hRK hR𝒪 hR hRinj s c hc hi₀ hi₀1 hZF
      (𝒪.valuation_le_one Z) ?_
    have h : residue 𝒪 (Sb - Z ^ p) = 0 := by rw [map_sub, map_pow, hzp, sub_self]
    rwa [residue_eq_zero_iff, valuation_lt_one_iff] at h
  obtain ⟨y, hyE, hxy⟩ := FrobeniusClosedBasis.exists_eq_sum_pow_mul_pow_of_subfield p
    (𝒪.residueSubfield K) E (fun c hc ↦ IntermediateField.algebraMap_mem _
      (⟨c, hc⟩ : 𝒪.residueSubfield K))
    (IntermediateField.mem_adjoin_simple_self _ _) htr
    (fun e he ↦ isSeparable_algebraMap (⟨e, he⟩ :
      IntermediateField.adjoin (𝒪.residueSubfield K) {residue 𝒪 x}))
    (residue_mem_adjoin_of_mem_closure K htr hSF) hρ
  choose Y hYF hYres using fun j ↦ exists_residue_eq_of_mem_adjoin K x (hyE j)
  refine ⟨p, fun j ↦ Y j, fun j ↦ ⟨hYF j, 𝒪.valuation_le_one _⟩, ?_⟩
  have h : residue 𝒪 (x - ∑ k ∈ Finset.range p, Y k ^ p * Sb ^ k) = 0 := by
    simp only [map_sub, map_sum, map_mul, map_pow, hYres]
    rw [← hxy, sub_self]
  rw [residue_eq_zero_iff, valuation_lt_one_iff] at h
  simpa [Sb] using h

end ValuationSubring

namespace ValuationSubring

open IsLocalRing

universe u

variable {Ω : Type u} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- **Lifts of a Frobenius-closed basis for `K(x)`.** In Ohm's setting in characteristic `p`, with
`K` of rank one relative to `Ω` (`hrk`), the partial-fraction monomials `xⁱ`, `(x - a)⁻ⁱ`
(`p ∤ i`, `a` running over representatives of the residues of `K`) are lifts of a
Frobenius-closed basis of `k(x̄)`: they have value `1`, are valuation independent over `K`
(`hval`), satisfy (P3), and every element of `K(x)` is approximated, up to an error of value
`< 1`, by a `K`-combination of `1` and their `p ^ n`-th powers. -/
theorem exists_frobeniusLift_approx_of_closure {p : ℕ} [hp : Fact p.Prime] [CharP Ω p]
    [CharP (ResidueField 𝒪) p] {K : Subfield Ω} [IsAlgClosed K] {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    (hrk : ∀ s ∈ K, ∀ t : Ω, s ≠ 0 → t ≠ 0 → 𝒪.valuation s < 1 →
      ∃ N : ℕ, 𝒪.valuation s ^ N < 𝒪.valuation t) :
    ∃ (ι : Type u) (w : ι → Ω),
      (∀ i, w i ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) ∧
      (∀ i, 𝒪.valuation (w i) = 1) ∧
      (∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) →
        ∀ i ∈ s, 𝒪.valuation (c i) ≤ 𝒪.valuation (∑ j ∈ s, c j * w j)) ∧
      (∀ (s : Finset ι) (c : ι → Ω), (∀ i ∈ s, c i ∈ K) → (∀ i ∈ s, 𝒪.valuation (c i) ≤ 1) →
        (∃ i ∈ s, 𝒪.valuation (c i) = 1) →
        ∃ (N : ℕ) (y : ℕ → Ω), (∀ k, y k ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}) ∧
          𝒪.valuation (y k) ≤ 1) ∧
          𝒪.valuation ((x : Ω) - ∑ k ∈ Finset.range N, y k ^ p * (∑ i ∈ s, c i * w i) ^ k) < 1) ∧
      ∀ α ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}),
        ∃ (s : Finset (ι × ℕ)) (d : ι × ℕ → Ω), (∀ j ∈ s, d j ∈ K) ∧
          ∃ d₀ ∈ K, 𝒪.valuation (α - d₀ - ∑ j ∈ s, d j * w j.1 ^ p ^ j.2) < 1 := by
  obtain ⟨R, hRK, hR𝒪, hR, hRinj⟩ := exists_residue_representatives (𝒪 := 𝒪) K
  have hxF : (x : Ω) ∈ Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}) :=
    Subfield.subset_closure (Or.inr rfl)
  refine ⟨{j // ¬ p ∣ partialFractionExponent R j}, fun i ↦ partialFractionLift (x : Ω) R i.1,
    fun i ↦ ?_, fun i ↦ valuation_partialFractionLift htr hRK hR𝒪 i.1, ?_,
    fun s c hc hc1 hunit ↦ exists_sub_sum_pow_mul_partialFractionLift_lt htr hrk hRK hR𝒪 hR hRinj
      s c hc hc1 hunit,
    fun α hα ↦ exists_sub_sum_partialFractionLift_lt htr hrk hRK hR𝒪 hR hp.out hα⟩
  · rcases i with ⟨m | ⟨⟨a, ha⟩, i⟩, -⟩
    · exact pow_mem hxF m
    · exact pow_mem (inv_mem (sub_mem hxF (Subfield.subset_closure (Or.inl (hRK ha))))) _
  · exact valuation_le_valuation_sum_of_linearIndependent _
      ((linearIndependent_residue_partialFractionLift htr hRK hR𝒪 hRinj).comp Subtype.val
        Subtype.val_injective)

end ValuationSubring
