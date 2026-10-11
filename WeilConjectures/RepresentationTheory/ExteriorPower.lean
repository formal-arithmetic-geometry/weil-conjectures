/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.RepresentationTheory.Constituents

/-!
# The exterior powers of a filtered representation

Let `U ⊆ V` be a subspace. The `n`-th exterior power `⋀ⁿ V` is filtered by the subspaces
`F_j = span {v₁ ∧ ⋯ ∧ vₙ | at least j of the vᵢ lie in U}`
(`exteriorPower.countSpan`), with `F_0 = ⋀ⁿ V` and `F_{n+1} = 0`, and the graded pieces are

$$
F_j / F_{j+1} \cong \textstyle\bigwedge^j U \otimes \bigwedge^{n-j} (V / U),
$$

via `u₁ ∧ ⋯ ∧ u_j ⊗ x̄₁ ∧ ⋯ ∧ x̄_l ↦ u₁ ∧ ⋯ ∧ u_j ∧ s(x̄₁) ∧ ⋯ ∧ s(x̄_l)` for a linear
section `s` of `V → V / U`. When `U` is a subrepresentation, the `F_j` are
subrepresentations and these isomorphisms are equivariant: changing the section changes the
image by an element of `F_{j+1}`.

## Main definitions

- `exteriorPower.countSpan`: the filtration `F_j` of `⋀ⁿ V`.
- `exteriorPower.wedge`: the product `⋀ʲ V × ⋀ˡ V → ⋀ʲ⁺ˡ V`.

## Blueprint

- `lem-mg-filtered-exterior-power`: the exterior power of a filtered representation.
-/

@[expose] public section

open TensorProduct

namespace exteriorPower

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

open Classical in
/-- The subspace of `⋀ⁿ V` spanned by the wedges `v₁ ∧ ⋯ ∧ vₙ` with at least `j` of the `vᵢ` in
the subspace `P`. -/
noncomputable def countSpan (P : Submodule k V) (n j : ℕ) : Submodule k (⋀[k]^n V) :=
  Submodule.span k {x | ∃ v : Fin n → V,
    j ≤ (Finset.univ.filter fun i ↦ v i ∈ P).card ∧ ιMulti k n v = x}

variable (P : Submodule k V) (n : ℕ)

open Classical in
theorem ιMulti_mem_countSpan {j : ℕ} (v : Fin n → V)
    (hv : j ≤ (Finset.univ.filter fun i ↦ v i ∈ P).card) : ιMulti k n v ∈ countSpan P n j :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem countSpan_succ_le (j : ℕ) : countSpan P n (j + 1) ≤ countSpan P n j :=
  Submodule.span_mono fun _ ⟨v, hv, hx⟩ ↦ ⟨v, (Nat.le_succ j).trans hv, hx⟩

theorem countSpan_anti {i j : ℕ} (h : i ≤ j) : countSpan P n j ≤ countSpan P n i :=
  Submodule.span_mono fun _ ⟨v, hv, hx⟩ ↦ ⟨v, h.trans hv, hx⟩

theorem countSpan_zero : countSpan P n 0 = ⊤ := by
  refine eq_top_iff.2 ((ιMulti_span (R := k) (n := n) (M := V)).symm.le.trans ?_)
  exact Submodule.span_le.2 fun _ ⟨v, hv⟩ ↦ Submodule.subset_span ⟨v, Nat.zero_le _, hv⟩

theorem countSpan_eq_bot {j : ℕ} (h : n < j) : countSpan P n j = ⊥ := by
  classical
  refine (Submodule.span_eq_bot).2 fun _ ⟨v, hv, _⟩ ↦ ?_
  have := (Finset.card_filter_le Finset.univ fun i ↦ v i ∈ P).trans_eq (Finset.card_fin n)
  omega

/-- A linear map preserving `P` preserves the filtration. -/
theorem map_mem_countSpan {f : V →ₗ[k] V} (hf : ∀ x ∈ P, f x ∈ P) {j : ℕ} {x : ⋀[k]^n V}
    (hx : x ∈ countSpan P n j) : map n f x ∈ countSpan P n j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [map_apply_ιMulti]
    refine ιMulti_mem_countSpan P n _ (hv.trans (Finset.card_le_card fun i hi ↦ ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hf _ hi
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- **Perturbing a wedge by vectors of `P`.** If `a` has at least `j` entries in `P` on a set `J`
of indices, and `y` is a family of vectors of `P` vanishing on `J`, then
`ι(a + y) - ι(a)` lies in the next filtration step `F_{j+1}`: expanding multilinearly, every other
term has an extra entry in `P`, or a zero entry. -/
theorem ιMulti_add_sub_ιMulti_mem_countSpan {j : ℕ} (a y : Fin n → V) (J : Finset (Fin n))
    (hJ : j ≤ J.card) (haJ : ∀ i ∈ J, a i ∈ P) (hyJ : ∀ i ∈ J, y i = 0) (hy : ∀ i, y i ∈ P) :
    ιMulti k n (a + y) - ιMulti k n a ∈ countSpan P n (j + 1) := by
  classical
  have h : ιMulti k n (a + y) = ∑ s : Finset (Fin n), ιMulti k n (s.piecewise a y) :=
    (ιMulti k n).toMultilinearMap.map_add_univ a y
  rw [h, ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), Finset.piecewise_univ,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hs' : s ≠ Finset.univ := Finset.ne_of_mem_erase hs
  by_cases hJs : J ⊆ s
  · -- an extra entry in `P` outside `s`
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.2 hs')
    refine ιMulti_mem_countSpan P n _ ?_
    have hi₀J : i₀ ∉ J := fun h ↦ hi₀ (hJs h)
    calc j + 1 ≤ (insert i₀ J).card := by rw [Finset.card_insert_of_notMem hi₀J]; omega
      _ ≤ _ := Finset.card_le_card fun i hi ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hi₀]
          exact hy _
        · rw [Finset.piecewise_eq_of_mem _ _ _ (hJs hi)]
          exact haJ i hi
  · -- a zero entry
    obtain ⟨i, hiJ, his⟩ := Finset.not_subset.1 hJs
    rw [(ιMulti k n).map_coord_zero i (by rw [Finset.piecewise_eq_of_notMem _ _ _ his, hyJ i hiJ])]
    exact zero_mem _

/-- The wedge product `⋀ʲ V × ⋀ˡ V → ⋀ⁿ V`, for `j + l = n`, as a bilinear map: the product in the
exterior algebra. -/
noncomputable def wedge {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j V →ₗ[k] ⋀[k]^l V →ₗ[k] ⋀[k]^n V :=
  LinearMap.mk₂ k (fun x y ↦ ⟨(x : ExteriorAlgebra k V) * y,
    h ▸ SetLike.mul_mem_graded x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

@[simp]
theorem coe_wedge_apply {j l : ℕ} (h : j + l = n) (x : ⋀[k]^j V) (y : ⋀[k]^l V) :
    (wedge n h x y : ExteriorAlgebra k V) = x * y :=
  rfl

theorem wedge_ιMulti_ιMulti {j l : ℕ} (a : Fin j → V) (b : Fin l → V) :
    wedge (j + l) rfl (ιMulti k j a) (ιMulti k l b) = ιMulti k (j + l) (Fin.append a b) :=
  Subtype.ext (by simp [ExteriorAlgebra.ιMulti_mul_ιMulti])

/-! ### The graded pieces -/

section Graded

variable {P} (s : V ⧸ P →ₗ[k] V)

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → ⋀ⁿ V`, `u ⊗ x̄ ↦ u ∧ s(x̄)`, for a linear section `s` of the
quotient map and `j + l = n`. -/
noncomputable def wedgeSection {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P) →ₗ[k] ⋀[k]^n V :=
  TensorProduct.lift ((wedge n h).compl₁₂ (map j P.subtype) (map l s))

theorem wedgeSection_tmul_ιMulti {j l : ℕ} (u : Fin j → P) (x : Fin l → V ⧸ P) :
    wedgeSection (j + l) s rfl (ιMulti k j u ⊗ₜ ιMulti k l x) =
      ιMulti k (j + l) (Fin.append (P.subtype ∘ u) (s ∘ x)) := by
  rw [wedgeSection, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, map_apply_ιMulti,
    map_apply_ιMulti, wedge_ιMulti_ιMulti]

open Classical in
theorem card_le_filter_append {j l : ℕ} (u : Fin j → P) (x : Fin l → V) :
    j ≤ (Finset.univ.filter fun i ↦ Fin.append (P.subtype ∘ u) x i ∈ P).card := by
  calc j = (Finset.univ.map (Fin.castAddEmb l)).card := by simp
    _ ≤ _ := Finset.card_le_card fun i hi ↦ by
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hi
      simp

theorem wedgeSection_mem_countSpan {j l : ℕ} (h : j + l = n)
    (t : ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P)) : wedgeSection n s h t ∈ countSpan P n j := by
  subst h
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | tmul x y =>
    have hx : x ∈ Submodule.span k (Set.range (ιMulti k j)) := by
      rw [ιMulti_span]; exact Submodule.mem_top
    have hy : y ∈ Submodule.span k (Set.range (ιMulti k l)) := by
      rw [ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        rw [wedgeSection_tmul_ιMulti]
        exact ιMulti_mem_countSpan P _ _ (card_le_filter_append u _)
      | zero => simp
      | add y y' _ _ hy hy' => simpa [TensorProduct.tmul_add] using add_mem hy hy'
      | smul a y _ hy => simpa [TensorProduct.tmul_smul] using Submodule.smul_mem _ a hy
    | zero => simp
    | add x x' _ _ hx hx' => simpa [TensorProduct.add_tmul] using add_mem hx hx'
    | smul a x _ hx =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ a hx

/-- The graded piece `F_j ⧸ F_{j+1}` of the filtration of `⋀ⁿ V`. -/
abbrev Graded (n j : ℕ) : Type _ :=
  countSpan P n j ⧸ (countSpan P n (j + 1)).comap (countSpan P n j).subtype

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}`. -/
noncomputable def toGraded {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P) →ₗ[k] Graded (P := P) n j :=
  Submodule.mkQ _ ∘ₗ (wedgeSection n s h).codRestrict _ (wedgeSection_mem_countSpan n s h)

variable {s} in
/-- `u ∧ s(x̄)` exhausts the graded piece `F_j ⧸ F_{j+1}`: a wedge with exactly `j` entries in `P`
is, modulo `F_{j+1}`, the wedge of these entries with the sections of the classes of the others,
up to a sign. -/
theorem toGraded_surjective (hs : ∀ x, P.mkQ (s x) = x) {j l : ℕ} (h : j + l = n) :
    Function.Surjective (toGraded n s h) := by
  classical
  subst h
  intro q
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, hv, rfl⟩ := hz
    set J := Finset.univ.filter fun i ↦ v i ∈ P
    rcases hv.lt_or_eq with hlt | heq
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
      exact ιMulti_mem_countSpan P _ v hlt
    -- the wedge `v'` with the entries outside `J` replaced by the sections of their classes
    set v' : Fin (j + l) → V := fun i ↦ if i ∈ J then v i else s (P.mkQ (v i))
    have hv'J (i) (hi : i ∈ J) : v' i = v i := if_pos hi
    have hv'Jc (i) (hi : i ∉ J) : v' i = s (P.mkQ (v i)) := if_neg hi
    have hJmem (i) (hi : i ∈ J) : v i ∈ P := (Finset.mem_filter.1 hi).2
    have hdiff : ιMulti k (j + l) (v' + (v - v')) - ιMulti k (j + l) v' ∈
        countSpan P (j + l) (j + 1) := by
      refine ιMulti_add_sub_ιMulti_mem_countSpan P _ v' (v - v') J heq.le
        (fun i hi ↦ by rw [hv'J i hi]; exact hJmem i hi)
        (fun i hi ↦ by rw [Pi.sub_apply, hv'J i hi, sub_self]) fun i ↦ ?_
      by_cases hi : i ∈ J
      · simp [hv'J i hi]
      · rw [Pi.sub_apply, hv'Jc i hi, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
          ← Submodule.mkQ_apply P (s _), hs, Submodule.mkQ_apply, sub_self]
    rw [add_sub_cancel] at hdiff
    have hv'mem : ιMulti k (j + l) v' ∈ countSpan P (j + l) j :=
      ιMulti_mem_countSpan P _ _ (heq.le.trans (Finset.card_le_card fun i hi ↦
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hv'J i hi]; exact hJmem i hi⟩))
    -- reorder `v'` with the entries of `J` first
    have hcardJ : Fintype.card {i // i ∈ J} = j := by
      rw [Fintype.card_coe, ← heq]
    have hcardJc : Fintype.card {i // i ∉ J} = l := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, ← heq, Fintype.card_fin]
      omega
    let e₁ : Fin j ≃ {i // i ∈ J} := (Fintype.equivFinOfCardEq hcardJ).symm
    let e₂ : Fin l ≃ {i // i ∉ J} := (Fintype.equivFinOfCardEq hcardJc).symm
    let σ : Equiv.Perm (Fin (j + l)) :=
      finSumFinEquiv.symm.trans ((e₁.sumCongr e₂).trans (Equiv.sumCompl fun i ↦ i ∈ J))
    let u : Fin j → P := fun a ↦ ⟨v (e₁ a), hJmem _ (e₁ a).2⟩
    let x : Fin l → V ⧸ P := fun b ↦ P.mkQ (v (e₂ b))
    have hσ : v' ∘ σ = Fin.append (P.subtype ∘ u) (s ∘ x) := by
      funext i
      refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
      · simp [σ, u, hv'J _ (e₁ a).2]
      · simp [σ, x, hv'Jc _ (e₂ b).2]
    have hperm := (ιMulti k (j + l)).map_perm v' σ
    rw [hσ, ← wedgeSection_tmul_ιMulti] at hperm
    have h1 : toGraded (j + l) s rfl (ιMulti k j u ⊗ₜ ιMulti k l x) =
        Submodule.Quotient.mk ⟨Equiv.Perm.sign σ • ιMulti k (j + l) v',
          Submodule.smul_mem _ _ hv'mem⟩ :=
      congrArg _ (Subtype.ext hperm)
    refine ⟨(Equiv.Perm.sign σ) • (ιMulti k j u ⊗ₜ ιMulti k l x), ?_⟩
    rw [map_zsmul_unit, h1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      Submodule.mem_comap]
    convert neg_mem hdiff using 1
    simp [smul_smul]
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | smul c x hx ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨c • a, by rw [map_smul, ha]; rfl⟩

variable (P) in
/-- The graded pieces telescope: `∑_{i < m} dim F_i ⧸ F_{i+1} + dim F_m = dim ⋀ⁿ V`. -/
theorem sum_finrank_graded_add [FiniteDimensional k V] (m : ℕ) :
    ∑ i ∈ Finset.range m, Module.finrank k (Graded (P := P) n i) +
      Module.finrank k (countSpan P n m) = Module.finrank k (⋀[k]^n V) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, zero_add, countSpan_zero P n, finrank_top]
  | succ m ih =>
    rw [Finset.sum_range_succ, add_assoc, ← ih]
    congr 1
    rw [← Submodule.finrank_quotient_add_finrank
      ((countSpan P n (m + 1)).comap (countSpan P n m).subtype),
      (Submodule.comapSubtypeEquivOfLe (countSpan_succ_le P n m)).finrank_eq]

/-- **The graded pieces of the filtration of `⋀ⁿ V`**: for a finite-dimensional `V`, the map
`⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}` is bijective. It is surjective, and the dimensions agree:
`∑ⱼ (dim P choose j) (dim V/P choose n - j) = (dim V choose n)` (Vandermonde). -/
theorem toGraded_bijective [FiniteDimensional k V] (hs : ∀ x, P.mkQ (s x) = x) {j l : ℕ}
    (h : j + l = n) : Function.Bijective (toGraded n s h) := by
  set p := Module.finrank k P
  set q := Module.finrank k (V ⧸ P)
  have hdim (i : ℕ) (hi : i ≤ n) : Module.finrank k (⋀[k]^i P ⊗[k] ⋀[k]^(n - i) (V ⧸ P)) =
      p.choose i * q.choose (n - i) := by
    rw [Module.finrank_tensorProduct, finrank_eq, finrank_eq]
  have hle (i : ℕ) (hi : i ≤ n) :
      Module.finrank k (Graded (P := P) n i) ≤ p.choose i * q.choose (n - i) :=
    (hdim i hi) ▸ by
      have hr := LinearMap.finrank_range_le (toGraded n s (Nat.add_sub_cancel' hi))
      rwa [LinearMap.range_eq_top.2 (toGraded_surjective n hs (Nat.add_sub_cancel' hi)),
        finrank_top] at hr
  have hsum : ∑ i ∈ Finset.range (n + 1), Module.finrank k (Graded (P := P) n i) =
      ∑ i ∈ Finset.range (n + 1), p.choose i * q.choose (n - i) := by
    have := sum_finrank_graded_add P n (n + 1)
    rw [countSpan_eq_bot P n (Nat.lt_succ_self n), finrank_bot, add_zero, finrank_eq,
      ← Submodule.finrank_quotient_add_finrank P, Nat.add_comm (Module.finrank k (V ⧸ P)),
      Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    exact this
  have heq := (Finset.sum_eq_sum_iff_of_le fun i hi ↦
    hle i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).1 hsum j
    (Finset.mem_range.2 (by omega))
  have hl : l = n - j := by omega
  subst hl
  refine ⟨?_, toGraded_surjective n hs h⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
    (toGraded_surjective n hs h)
  rw [hdim j (by omega), heq]

end Graded

end exteriorPower

/-! ### The filtration of the exterior power of a representation -/

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The filtration `F_j = span {v₁ ∧ ⋯ ∧ vₙ | at least j of the vᵢ lie in P}` of `⋀ⁿ V` by
subrepresentations, for a subrepresentation `P` of `ρ`. -/
noncomputable def exteriorPowerFiltration (P : Subrepresentation ρ) (n j : ℕ) :
    Subrepresentation (ρ.exteriorPower n) where
  toSubmodule := exteriorPower.countSpan P.toSubmodule n j
  apply_mem_toSubmodule w _ hx :=
    exteriorPower.map_mem_countSpan _ n (fun _ hy ↦ P.apply_mem_toSubmodule w hy) hx

variable (P : Subrepresentation ρ) (n : ℕ)

theorem exteriorPowerFiltration_succ_le (j : ℕ) :
    P.exteriorPowerFiltration n (j + 1) ≤ P.exteriorPowerFiltration n j :=
  exteriorPower.countSpan_succ_le _ n j

theorem exteriorPowerFiltration_zero : P.exteriorPowerFiltration n 0 = ⊤ :=
  toSubmodule_injective (exteriorPower.countSpan_zero _ n)

theorem exteriorPowerFiltration_eq_bot {j : ℕ} (h : n < j) : P.exteriorPowerFiltration n j = ⊥ :=
  toSubmodule_injective (exteriorPower.countSpan_eq_bot _ n h)

/-- The quotient map `V → V ⧸ P` intertwines `ρ` with the quotient representation. -/
theorem quotient_apply_mkQ (w : W) (x : V) :
    P.quotient w (P.toSubmodule.mkQ x) = P.toSubmodule.mkQ (ρ w x) :=
  rfl

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}` is equivariant: changing `ρ(w) s(x̄)` into
`s(ρ(w) x̄)` changes the wedge by an element of `F_{j+1}`. -/
theorem toGraded_comp_map (s : V ⧸ P.toSubmodule →ₗ[k] V) (hs : ∀ x, P.toSubmodule.mkQ (s x) = x)
    {j l : ℕ} (h : j + l = n) (w : W) :
    exteriorPower.toGraded n s h ∘ₗ ((P.toRepresentation.exteriorPower j).tprod
      (P.quotient.exteriorPower l) w) =
      (P.exteriorPowerFiltration n j).subquotient (P.exteriorPowerFiltration n (j + 1)) w ∘ₗ
        exteriorPower.toGraded n s h := by
  subst h
  refine TensorProduct.ext (exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦
    exteriorPower.linearMap_ext (AlternatingMap.ext fun x ↦ ?_)))
  simp only [LinearMap.compAlternatingMap_apply, Representation.tprod_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  change exteriorPower.wedgeSection (j + l) s rfl
      (exteriorPower.map j (P.toRepresentation w) (exteriorPower.ιMulti k j u) ⊗ₜ
        exteriorPower.map l (P.quotient w) (exteriorPower.ιMulti k l x)) -
      exteriorPower.map (j + l) (ρ w) (exteriorPower.wedgeSection (j + l) s rfl
        (exteriorPower.ιMulti k j u ⊗ₜ exteriorPower.ιMulti k l x)) ∈ _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.wedgeSection_tmul_ιMulti, exteriorPower.wedgeSection_tmul_ιMulti,
    exteriorPower.map_apply_ιMulti]
  -- the two wedges differ by vectors of `P` in the last `l` entries
  set a : Fin (j + l) → V := ρ w ∘ Fin.append (P.toSubmodule.subtype ∘ u) (s ∘ x)
  set y : Fin (j + l) → V := Fin.append (0 : Fin j → V)
    (fun b ↦ s (P.quotient w (x b)) - ρ w (s (x b)))
  have hay : Fin.append (P.toSubmodule.subtype ∘ (P.toRepresentation w ∘ u))
      (s ∘ (P.quotient w ∘ x)) = a + y := by
    funext i
    refine Fin.addCases (fun c ↦ ?_) (fun b ↦ ?_) i
    · simp [a, y]
      rfl
    · simp [a, y]
  rw [hay]
  refine exteriorPower.ιMulti_add_sub_ιMulti_mem_countSpan _ _ a y
    (Finset.univ.map (Fin.castAddEmb l)) (by simp) (fun i hi ↦ ?_) (fun i hi ↦ ?_) fun i ↦ ?_
  · obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hi
    simpa [a] using P.apply_mem_toSubmodule w (u c).2
  · obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hi
    simp [y]
  · refine Fin.addCases (fun c ↦ ?_) (fun b ↦ ?_) i
    · simp [y]
    · simp only [y, Fin.append_right]
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hs, ← quotient_apply_mkQ, hs, sub_self]

/-- **The graded pieces of the exterior power of a representation.** For a subrepresentation `P`
of a finite-dimensional representation `ρ`, the `j`-th graded piece `F_j ⧸ F_{j+1}` of the
filtration of `⋀ⁿ V` is equivalent to `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P)`, `j + l = n`.
(blueprint: `lem-mg-filtered-exterior-power`) -/
noncomputable def exteriorPowerGradedEquiv [FiniteDimensional k V] {j l : ℕ} (h : j + l = n) :
    ((P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower l)).Equiv
      ((P.exteriorPowerFiltration n j).subquotient (P.exteriorPowerFiltration n (j + 1))) :=
  have hs := P.toSubmodule.mkQ.exists_rightInverse_of_surjective P.toSubmodule.range_mkQ
  .mk (.ofBijective _ (exteriorPower.toGraded_bijective n (s := hs.choose)
      (fun x ↦ LinearMap.congr_fun hs.choose_spec x) h))
    (P.toGraded_comp_map n hs.choose (fun x ↦ LinearMap.congr_fun hs.choose_spec x) h)

end Subrepresentation
