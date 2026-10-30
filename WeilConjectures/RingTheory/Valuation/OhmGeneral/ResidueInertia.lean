/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.OhmGeneral.ResiduePth

/-!
# Residues of the inertia field: `p`-th roots

Let `Ω` be separably closed and separable over a subfield `F`, `𝒪` a valuation subring of `Ω`
with residue characteristic `p`, `D` and `I` the decomposition and inertia groups of `𝒪` over `F`.

- `ValuationSubring.mem_inertiaSubgroup_of_forall_isIntegral`: an element of `D` acting trivially
  modulo `𝔪` on the integral closure of `𝒪 ∩ F` lies in `I`.
- `ValuationSubring.apply_eq_of_forall_valuation_sub_lt_one`: if `z` is fixed by `I` and `δ ∈ D`
  acts trivially modulo `𝔪` on the integral elements fixed by `Gal(Ω/F(z))`, then `δ z = z`
  (surjectivity of the decomposition group onto residue automorphisms).
- `ValuationSubring.exists_valuation_sub_lt_one_of_mem_inertiaField_of_pow`: if `z ∈ 𝒪` lies in
  the inertia field and `z̄ ^ p` is a residue of `F`, then so is `z̄`.
- `ValuationSubring.residue_pow_ne_of_mem_inertiaField`: **(R3)** in Ohm's setting, `x̄` is not a
  `p`-th power in the residue field of the inertia field.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped Pointwise

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] {𝒪 : ValuationSubring Ω}

/-- Elements of the decomposition group preserve the maximal ideal. -/
lemma valuation_decompositionSubgroup_apply_lt_one_iff {F : Subfield Ω}
    (σ : 𝒪.decompositionSubgroup F) (y : Ω) :
    𝒪.valuation ((σ : Ω ≃ₐ[F] Ω) y) < 1 ↔ 𝒪.valuation y < 1 := by
  refine ⟨fun h ↦ ?_, valuation_apply_lt_one 𝒪 (σ : Ω ≃ₐ[F] Ω).toRingEquiv
    (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ hx)
    (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ⁻¹ hx)⟩
  have := valuation_apply_lt_one 𝒪 ((σ⁻¹ : 𝒪.decompositionSubgroup F) : Ω ≃ₐ[F] Ω).toRingEquiv
    (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ⁻¹ hx)
    (fun _ hx ↦ decompositionSubgroup_apply_mem 𝒪 σ hx) h
  simpa using this

/-- **Inertia via the integral closure.** If `Ω / F` is algebraic and `σ` in the decomposition
group acts trivially modulo `𝔪` on the integral closure of `𝒪 ∩ F`, then `σ` lies in the inertia
group. -/
theorem mem_inertiaSubgroup_of_forall_isIntegral (F : Subfield Ω) [Algebra.IsAlgebraic F Ω]
    (σ : 𝒪.decompositionSubgroup F)
    (hσ : ∀ b : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) b →
      𝒪.valuation ((σ : Ω ≃ₐ[F] Ω) b - b) < 1) :
    σ ∈ 𝒪.inertiaSubgroup F := by
  rw [inertiaSubgroup, MonoidHom.mem_ker]
  ext y
  obtain ⟨y, rfl⟩ := residue_surjective y
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply,
    ← IsLocalRing.ResidueField.residue_smul, RingAut.one_apply, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, valuation_lt_one_iff]
  obtain ⟨s, hs, hvs, ht⟩ := exists_isIntegral_mul_isIntegral F y.2
    (Algebra.IsAlgebraic.isAlgebraic (y : Ω))
  set τ := (σ : Ω ≃ₐ[F] Ω)
  have hσs : 𝒪.valuation (τ s) = 1 := by
    rw [← add_sub_cancel s (τ s), Valuation.map_add_eq_of_lt_left _ (by rw [hvs]; exact hσ s hs),
      hvs]
  have hσs0 : τ s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hσs
    exact zero_ne_one hσs
  have heq : τ y - y = (τ (y * s) - y * s - y * (τ s - s)) / τ s := by
    rw [map_mul]
    field_simp
    ring
  have hy : 𝒪.valuation (y : Ω) ≤ 1 := (valuation_le_one_iff _ _).2 y.2
  have hcoe : ((σ • y - y : 𝒪) : Ω) = τ y - y := rfl
  rw [hcoe, heq, map_div₀, hσs, div_one]
  refine Valuation.map_sub_lt _ (hσ _ ht) ?_
  rw [map_mul, mul_comm]
  exact mul_lt_one_of_lt_of_le (hσ s hs) hy

/-- **Residue automorphisms come from the decomposition group.** Let `Ω` be separably closed and
separable over `F`, `z` an element of the inertia field and `δ` in the decomposition group. If
`δ` acts trivially modulo `𝔪` on the elements integral over `𝒪 ∩ F` and fixed by `Gal(Ω/F(z))`,
then `δ z = z`. (By surjectivity of the stabiliser of `𝔪` in `Gal(Ω/F(z))` onto the residue
automorphisms, `δ` agrees modulo `𝔪` with some `g` fixing `z`; then `g⁻¹ δ` is inertia.) -/
theorem apply_eq_of_forall_valuation_sub_lt_one [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω] {z : Ω} (hz : z ∈ 𝒪.inertiaField F) (δ : 𝒪.decompositionSubgroup F)
    (hδ : ∀ e : Ω, IsIntegral ↥(𝒪.toSubring ⊓ F.toSubring) e →
      (∀ σ : Ω ≃ₐ[F] Ω, σ z = z → σ e = e) → 𝒪.valuation ((δ : Ω ≃ₐ[F] Ω) e - e) < 1) :
    (δ : Ω ≃ₐ[F] Ω) z = z := by
  set R := 𝒪.toSubring ⊓ F.toSubring
  let := integralClosureMulSemiringAction (F := F) (R := R) inf_le_right
  let : TopologicalSpace (integralClosure R Ω) := ⊥
  have : DiscreteTopology (integralClosure R Ω) := ⟨rfl⟩
  have := IsSepClosed.isGalois_of_isSeparable (F := F) (Ω := Ω)
  set G := MulAction.stabilizer (Ω ≃ₐ[F] Ω) z
  have : CompactSpace G := isCompact_iff_compactSpace.1
    (Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral z)).isCompact
  have : ContinuousSMul G (integralClosure R Ω) := by
    refine continuousSMul_iff_stabilizer_isOpen.2 fun b ↦ ?_
    have := (stabilizer_isOpen_of_isIntegral (K := F) (b : Ω)).preimage
      (continuous_subtype_val (p := (· ∈ G)))
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    exact Subtype.ext_iff
  let A := FixedPoints.subring (integralClosure R Ω) G
  have : Algebra.IsInvariant A (integralClosure R Ω) G := ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
  let Q : Ideal (integralClosure R Ω) :=
    (maximalIdeal 𝒪).comap (integralClosureToValuationSubring F 1)
  have hQ (b : integralClosure R Ω) : b ∈ Q ↔ 𝒪.valuation (b : Ω) < 1 := by
    rw [Ideal.mem_comap, valuation_lt_one_iff]
    rfl
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  let δB : integralClosure R Ω ≃+* integralClosure R Ω :=
    MulSemiringAction.toRingEquiv _ _ (δ : Ω ≃ₐ[F] Ω)
  have hQδ : Q = Q.map (δB : integralClosure R Ω →+* integralClosure R Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [hQ, Ideal.mem_comap, hQ]
    exact (valuation_decompositionSubgroup_apply_lt_one_iff δ⁻¹ b).symm
  let δbar : (integralClosure R Ω ⧸ Q) ≃ₐ[A ⧸ Q.under A] (integralClosure R Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q δB hQδ) fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.quotientEquiv_mk, Ideal.Quotient.eq, hQ]
      exact hδ _ a.1.2 fun σ hσ ↦ congrArg Subtype.val (a.2 ⟨σ, hσ⟩)
  obtain ⟨g, hg⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (Q.under A) Q δbar
  have hgδ (b : integralClosure R Ω) :
      𝒪.valuation (((g : G) : Ω ≃ₐ[F] Ω) b - (δ : Ω ≃ₐ[F] Ω) b) < 1 := by
    have := DFunLike.congr_fun hg (Ideal.Quotient.mk Q b)
    rw [Ideal.Quotient.stabilizerHom_apply, AlgEquiv.ofRingEquiv_apply, Ideal.quotientEquiv_mk,
      Ideal.Quotient.eq, hQ] at this
    exact this
  have hgD : ((g : G) : Ω ≃ₐ[F] Ω) ∈ 𝒪.decompositionSubgroup F := by
    refine mem_decompositionSubgroup_of_forall_isIntegral F _ fun b hb ↦ ?_
    have h1 := hgδ ⟨b, hb⟩
    rw [← valuation_decompositionSubgroup_apply_lt_one_iff δ b]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← sub_sub_cancel (((g : G) : Ω ≃ₐ[F] Ω) b) ((δ : Ω ≃ₐ[F] Ω) b)]
      exact Valuation.map_sub_lt _ h h1
    · rw [← sub_add_cancel (((g : G) : Ω ≃ₐ[F] Ω) b) ((δ : Ω ≃ₐ[F] Ω) b)]
      exact Valuation.map_add_lt _ h1 h
  set γ : 𝒪.decompositionSubgroup F := ⟨_, hgD⟩
  have hI : γ⁻¹ * δ ∈ 𝒪.inertiaSubgroup F := by
    refine mem_inertiaSubgroup_of_forall_isIntegral F _ fun b hb ↦ ?_
    rw [← valuation_decompositionSubgroup_apply_lt_one_iff γ, Subgroup.coe_mul, Subgroup.coe_inv,
      map_sub, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply,
      Valuation.map_sub_swap]
    exact hgδ ⟨b, hb⟩
  have := (mem_inertiaField_iff 𝒪).1 hz _ hI
  rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_eq] at this
  rw [this]
  exact (g : G).2

/-- **`p`-th roots of residues in the inertia field.** Let `Ω` be separably closed and separable
over `F`, with residue characteristic `p`. If `z ∈ 𝒪` lies in the inertia field and `z̄ ^ p` is a
residue of `F`, then so is `z̄`.

Proof: every `σ` in the decomposition group `D` satisfies `σ z ≡ z`. Let `c` run over the
`D`-orbit of `z`, with `δ_c ∈ D` mapping `z` to `c`. The maps `ē ↦ (δ_c e)‾`, on the integral
elements `e` fixed by `Gal(Ω/F(z))`, are pairwise distinct
(`apply_eq_of_forall_valuation_sub_lt_one`), so by Dedekind's lemma some `e` has
`∑ (δ_c e)‾ ≠ 0`. The sums `∑ δ_c (z e)` and `∑ δ_c e` are fixed by `D`, so their residues
`z̄ ∑ (δ_c e)‾` and `∑ (δ_c e)‾` are residues of `F`. -/
theorem exists_valuation_sub_lt_one_of_mem_inertiaField_of_pow [IsSepClosed Ω] (F : Subfield Ω)
    [Algebra.IsSeparable F Ω] {p : ℕ} [Fact p.Prime] [CharP (ResidueField 𝒪) p] {z : Ω}
    (hz : z ∈ 𝒪) (hzL : z ∈ 𝒪.inertiaField F) {w : Ω} (hw : w ∈ F)
    (hzw : 𝒪.valuation (z ^ p - w) < 1) :
    ∃ b ∈ F, b ∈ 𝒪 ∧ 𝒪.valuation (z - b) < 1 := by
  classical
  set R := 𝒪.toSubring ⊓ F.toSubring
  -- the orbit of `z` under the decomposition group
  set O := ((minpoly F z).aroots Ω).toFinset.filter
    fun c ↦ ∃ σ : 𝒪.decompositionSubgroup F, (σ : Ω ≃ₐ[F] Ω) z = c
  have hmemO (σ : 𝒪.decompositionSubgroup F) : (σ : Ω ≃ₐ[F] Ω) z ∈ O := by
    refine Finset.mem_filter.2 ⟨?_, σ, rfl⟩
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral z), ?_⟩
    rw [← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hzO : z ∈ O := hmemO 1
  have hδ (c : Ω) : ∃ δ : 𝒪.decompositionSubgroup F, c ∈ O → (δ : Ω ≃ₐ[F] Ω) z = c := by
    by_cases hc : c ∈ O
    · obtain ⟨δ, hδ⟩ := (Finset.mem_filter.1 hc).2
      exact ⟨δ, fun _ ↦ hδ⟩
    · exact ⟨1, fun h ↦ absurd h hc⟩
  choose δ hδ using hδ
  -- sums over the orbit of elements fixed by `Gal(Ω/F(z))` are fixed by `D`
  have hinv (y : Ω) (hy : ∀ σ : Ω ≃ₐ[F] Ω, σ z = z → σ y = y) (σ : 𝒪.decompositionSubgroup F) :
      (σ : Ω ≃ₐ[F] Ω) (∑ c ∈ O, (δ c : Ω ≃ₐ[F] Ω) y) = ∑ c ∈ O, (δ c : Ω ≃ₐ[F] Ω) y := by
    rw [map_sum]
    have hσO (c : Ω) (hc : c ∈ O) : (σ : Ω ≃ₐ[F] Ω) c ∈ O := by
      rw [← hδ c hc]
      exact hmemO (σ * δ c)
    refine Finset.sum_nbij (fun c ↦ (σ : Ω ≃ₐ[F] Ω) c) hσO
      (fun c _ c' _ h ↦ (σ : Ω ≃ₐ[F] Ω).injective h) (fun c' hc' ↦ ?_) (fun c hc ↦ ?_)
    · refine ⟨((σ⁻¹ : 𝒪.decompositionSubgroup F) : Ω ≃ₐ[F] Ω) c', ?_, ?_⟩
      · rw [Finset.mem_coe, ← hδ c' hc']
        exact hmemO (σ⁻¹ * δ c')
      · rw [Subgroup.coe_inv, AlgEquiv.aut_inv]
        exact AlgEquiv.apply_symm_apply _ _
    · have h1 : ((δ ((σ : Ω ≃ₐ[F] Ω) c) : Ω ≃ₐ[F] Ω)⁻¹ * ((σ : Ω ≃ₐ[F] Ω) *
          (δ c : Ω ≃ₐ[F] Ω))) z = z := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hδ c hc, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_eq, hδ _ (hσO c hc)]
      have h2 := hy _ h1
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h2
      exact h2
  -- the integral elements fixed by `Gal(Ω/F(z))`
  let M : Submonoid (integralClosure R Ω) :=
    { carrier := {b | ∀ σ : Ω ≃ₐ[F] Ω, σ z = z → σ (b : Ω) = b}
      mul_mem' := fun {a b} ha hb σ hσ ↦ by
        rw [MulMemClass.coe_mul, map_mul, ha σ hσ, hb σ hσ]
      one_mem' := fun σ _ ↦ by rw [OneMemClass.coe_one, map_one] }
  have hmem (σ : 𝒪.decompositionSubgroup F) (b : integralClosure R Ω) :
      (σ : Ω ≃ₐ[F] Ω) b ∈ 𝒪 :=
    decompositionSubgroup_apply_mem 𝒪 σ (mem_of_isIntegral_of_le inf_le_left b.2)
  let φ (c : O) : M →* ResidueField 𝒪 :=
    ((residue 𝒪).toMonoidHom.comp
      (integralClosureToValuationSubring F (δ c : Ω ≃ₐ[F] Ω)).toMonoidHom).comp M.subtype
  have hφ (c : O) (b : M) : φ c b = residue 𝒪 ⟨(δ c : Ω ≃ₐ[F] Ω) b, hmem _ _⟩ := rfl
  have hφinj : Function.Injective φ := by
    intro c c' h
    by_contra hne
    have hzc : (((δ c')⁻¹ * δ c : 𝒪.decompositionSubgroup F) : Ω ≃ₐ[F] Ω) z ≠ z := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, hδ c c.2, AlgEquiv.aut_inv,
        Ne, AlgEquiv.symm_apply_eq, hδ c' c'.2]
      exact fun h' ↦ hne (Subtype.ext h')
    refine hzc (apply_eq_of_forall_valuation_sub_lt_one F hzL _ fun e he hfix ↦ ?_)
    have h1 := DFunLike.congr_fun h ⟨⟨e, he⟩, hfix⟩
    rw [hφ, hφ] at h1
    rw [← valuation_decompositionSubgroup_apply_lt_one_iff (δ c'), Subgroup.coe_mul,
      Subgroup.coe_inv, map_sub, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    exact (valuation_sub_lt_one_iff_residue_eq 𝒪 _ _).2 h1
  -- Dedekind's lemma
  obtain ⟨e, he⟩ : ∃ e : M, ∑ c : O, φ c e ≠ 0 := by
    by_contra! h
    have := Fintype.linearIndependent_iff.1
      ((linearIndependent_monoidHom M (ResidueField 𝒪)).comp φ hφinj) (fun _ ↦ 1)
      (funext fun e ↦ by simpa using h e)
    exact one_ne_zero (this ⟨z, hzO⟩)
  set e' : Ω := ((e : integralClosure R Ω) : Ω)
  have he' : ∀ σ : Ω ≃ₐ[F] Ω, σ z = z → σ e' = e' := e.2
  have he'𝒪 (σ : 𝒪.decompositionSubgroup F) : (σ : Ω ≃ₐ[F] Ω) e' ∈ 𝒪 := hmem σ e
  set w₁ := ∑ c ∈ O, (δ c : Ω ≃ₐ[F] Ω) (z * e')
  set w₂ := ∑ c ∈ O, (δ c : Ω ≃ₐ[F] Ω) e'
  have hw₁ : w₁ ∈ 𝒪 := Subring.sum_mem _ fun c _ ↦ by
    rw [map_mul]
    exact MulMemClass.mul_mem (decompositionSubgroup_apply_mem 𝒪 _ hz) (he'𝒪 _)
  have hw₂ : w₂ ∈ 𝒪 := Subring.sum_mem _ fun c _ ↦ he'𝒪 _
  obtain ⟨b₁, hb₁F, hb₁, hwb₁⟩ := exists_valuation_sub_lt_one_of_forall_decompositionSubgroup F
    hw₁ (hinv _ fun σ hσ ↦ by rw [map_mul, hσ, he' σ hσ])
  obtain ⟨b₂, hb₂F, -, hwb₂⟩ := exists_valuation_sub_lt_one_of_forall_decompositionSubgroup F
    hw₂ (hinv _ he')
  -- `w₁ ≡ z w₂`
  have hw₁₂ : 𝒪.valuation (z * w₂ - w₁) < 1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun c _ ↦ ?_
    rw [map_mul, ← sub_mul, map_mul, Valuation.map_sub_swap]
    exact mul_lt_one_of_lt_of_le
      (valuation_apply_sub_lt_one_of_pow_sub (δ c) hz hw hzw)
      ((valuation_le_one_iff _ _).2 (he'𝒪 _))
  -- `w₂` is a unit
  have hv₂ : 𝒪.valuation w₂ = 1 := by
    refine le_antisymm ((valuation_le_one_iff _ _).2 hw₂) (not_lt.1 fun h ↦ he ?_)
    have hres : residue 𝒪 ⟨w₂, hw₂⟩ = ∑ c : O, φ c e := by
      simp only [hφ]
      rw [← map_sum]
      congr 1
      ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (Finset.sum_coe_sort O fun c ↦ (δ c : Ω ≃ₐ[F] Ω) e').symm
    rw [← hres, residue_eq_zero_iff, valuation_lt_one_iff]
    exact h
  have hvb₂ : 𝒪.valuation b₂ = 1 := by
    rw [← add_sub_cancel w₂ b₂, Valuation.map_add_eq_of_lt_left _
      (by rwa [hv₂, Valuation.map_sub_swap]), hv₂]
  have hb₂0 : b₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvb₂
    exact zero_ne_one hvb₂
  refine ⟨b₁ / b₂, F.div_mem hb₁F hb₂F, ?_, ?_⟩
  · rw [← valuation_le_one_iff, map_div₀, hvb₂, div_one, valuation_le_one_iff]
    exact hb₁
  · have hdiff : z - b₁ / b₂ = (z * (b₂ - w₂) + (z * w₂ - w₁) + (w₁ - b₁)) / b₂ := by
      field_simp
      ring
    have h1 : 𝒪.valuation (z * (b₂ - w₂)) < 1 := by
      rw [map_mul, mul_comm, Valuation.map_sub_swap]
      exact mul_lt_one_of_lt_of_le hwb₂ ((valuation_le_one_iff _ _).2 hz)
    rw [hdiff, map_div₀, hvb₂, div_one]
    exact Valuation.map_add_lt _ (Valuation.map_add_lt _ h1 hw₁₂) hwb₁

/-- **(R3)** In Ohm's setting, `x̄` is not a `p`-th power in the residue field of the inertia field
of `K(x)`. -/
theorem residue_pow_ne_of_mem_inertiaField [IsSepClosed Ω] {p : ℕ} [hp : Fact p.Prime]
    [CharP (ResidueField 𝒪) p] (K : Subfield Ω) {x : 𝒪}
    (htr : Transcendental (𝒪.residueSubfield K) (residue 𝒪 x))
    [Algebra.IsSeparable (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)})) Ω] {w : 𝒪}
    (hw : (w : Ω) ∈ 𝒪.inertiaField (Subfield.closure ((K : Set Ω) ∪ {(x : Ω)}))) :
    residue 𝒪 w ^ p ≠ residue 𝒪 x := by
  intro hwx
  obtain ⟨b, hbF, hb, hwb⟩ := exists_valuation_sub_lt_one_of_mem_inertiaField_of_pow _ (p := p)
    w.2 hw (Subfield.subset_closure (Or.inr rfl))
    ((valuation_sub_lt_one_iff_residue_eq 𝒪 (pow_mem w.2 p) x.2).2 ((map_pow _ _ _).trans hwx))
  have hres : residue 𝒪 w = residue 𝒪 ⟨b, hb⟩ :=
    (valuation_sub_lt_one_iff_residue_eq 𝒪 w.2 hb).1 hwb
  exact IntermediateField.pow_ne_of_mem_adjoin_simple hp.out.one_lt htr
    (hres ▸ residue_mem_adjoin_of_mem_closure K htr (y := ⟨b, hb⟩) hbF) hwx

end ValuationSubring
