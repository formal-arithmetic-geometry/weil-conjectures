module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Maps.Basic
import Sheaf.Analysis.NormedSpace.FiniteUltrametricBestApproximation
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Logic.Denumerable
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Uniformly bounded algebraic coordinates in a countable ultrametric space

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent auxiliary for the geometric norm projection; an exact external
reference is WANTED (blueprint: lem-sfb-countable-normed-orthogonal-basis).

The coordinates are algebraic finite-support coordinates. No completeness of the
vector space and no convergence of infinite series are asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u v

namespace Padic

private lemma ultrametric_sum_bound
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W]
    (hu : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    {ι : Type*} (t : Finset ι) (f : ι → W) (D : ℝ) (hD : 0 ≤ D)
    (hf : ∀ i ∈ t, ‖f i‖ ≤ D) : ‖∑ i ∈ t, f i‖ ≤ D := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hD
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))))

private lemma coefficient_le_sup
    {K : Type*} [NormedField K] {ι : Type*} (a : ι →₀ K) (i : ι) :
    ‖a i‖ ≤ ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) := by
  classical
  by_cases hi : i ∈ a.support
  · exact_mod_cast (Finset.le_sup (f := fun j ↦ ‖a j‖₊) hi)
  · simp only [Finsupp.notMem_support_iff.mp hi, norm_zero]
    exact NNReal.coe_nonneg _

private lemma basis_image_bound
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]
    (hu : ∀ x y : Z, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    {ι : Type*} (b : Module.Basis ι K W) (f : W →ₗ[K] Z) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ j, ‖f (b j)‖ ≤ C) (a : ι →₀ K) :
    ‖f (b.repr.symm a)‖ ≤ C * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) := by
  classical
  rw [b.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [map_smul]
  apply ultrametric_sum_bound (K := K) hu a.support _ _
    (mul_nonneg hC (NNReal.coe_nonneg _))
  intro i hi
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _)).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (coefficient_le_sup a i) hC)

open Classical in
private lemma bounded_basis_topology
    {K : Type*} [NontriviallyNormedField K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    (hu : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    {ι : Type*} (b : Module.Basis ι K W) (c C : ℝ) (hc : 0 < c) (hC : c ≤ C)
    (hb : ∀ a : ι →₀ K,
      c * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) ≤ ‖b.repr.symm a‖ ∧
      ‖b.repr.symm a‖ ≤ C * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ)) :
    (∀ j : ι, Continuous (b.coord j)) ∧
    (∀ S : Set ι, Continuous (b.constr K (fun j ↦ if j ∈ S then b j else 0))) ∧
    (∀ σ : ι ↪ ι, Topology.IsEmbedding (b.constr K (fun j ↦ b (σ j)))) := by
  classical
  have hC0 : 0 ≤ C := hc.le.trans hC
  have hbn (i : ι) : ‖b i‖ ≤ C := by
    simpa using (hb (Finsupp.single i 1)).2
  have hcoef (x : W) (i : ι) : ‖b.repr x i‖ ≤ c⁻¹ * ‖x‖ := by
    have h := (hb (b.repr x)).1
    rw [b.repr.symm_apply_apply] at h
    have h' := mul_le_mul_of_nonneg_left (coefficient_le_sup (b.repr x) i) hc.le
    apply (le_inv_mul_iff₀ hc).2
    exact h'.trans h
  refine ⟨fun i ↦ (b.coord i |>.mkContinuous c⁻¹ (fun x ↦ hcoef x i)).continuous,
    fun S ↦ ?_, fun σ ↦ ?_⟩
  · let f := b.constr K (fun j ↦ if j ∈ S then b j else 0)
    have hf (j : ι) : ‖f (b j)‖ ≤ C := by
      simp only [f, Module.Basis.constr_basis]
      split_ifs <;> simp_all
    exact (f.mkContinuous (C / c) (fun x ↦ by
      have h := basis_image_bound hu b f C hC0 hf (b.repr x)
      rw [b.repr.symm_apply_apply] at h
      have h' := (hb (b.repr x)).1
      rw [b.repr.symm_apply_apply] at h'
      calc
        ‖f x‖ ≤ C * ((b.repr x).support.sup (fun j ↦ ‖b.repr x j‖₊) : NNReal) := h
        _ ≤ C * (c⁻¹ * ‖x‖) := mul_le_mul_of_nonneg_left
          ((le_inv_mul_iff₀ hc).2 h') hC0
        _ = C / c * ‖x‖ := by ring)).continuous
  · let f := b.constr K (fun j ↦ b (σ j))
    have hf (j : ι) : ‖f (b j)‖ ≤ C := by
      simpa only [f, Module.Basis.constr_basis] using hbn (σ j)
    have hfbound (x : W) : ‖f x‖ ≤ C / c * ‖x‖ := by
      have h := basis_image_bound hu b f C hC0 hf (b.repr x)
      rw [b.repr.symm_apply_apply] at h
      have h' := (hb (b.repr x)).1
      rw [b.repr.symm_apply_apply] at h'
      calc
        ‖f x‖ ≤ C * ((b.repr x).support.sup (fun j ↦ ‖b.repr x j‖₊) : NNReal) := h
        _ ≤ C * (c⁻¹ * ‖x‖) := mul_le_mul_of_nonneg_left
          ((le_inv_mul_iff₀ hc).2 h') hC0
        _ = C / c * ‖x‖ := by ring
    have hre (a : ι →₀ K) : b.repr (f (b.repr.symm a)) = a.embDomain σ := by
      apply b.repr.symm.injective
      simp only [b.repr.symm_apply_apply, b.repr_symm_apply,
        Finsupp.linearCombination_embDomain]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
        f, Module.Basis.constr_basis, Function.comp_apply]
    have hanti (x : W) : ‖x‖ ≤ C / c * ‖f x‖ := by
      have hl := (hb (b.repr (f x))).1
      rw [b.repr.symm_apply_apply] at hl
      have hs : ((b.repr x).support.sup (fun j ↦ ‖b.repr x j‖₊) : NNReal) ≤
          (b.repr (f x)).support.sup (fun j ↦ ‖b.repr (f x) j‖₊) := by
        apply Finset.sup_le
        intro j hj
        have hh := coefficient_le_sup (b.repr (f x)) (σ j)
        have hr := hre (b.repr x)
        simp only [b.repr.symm_apply_apply] at hr
        have he : b.repr (f x) (σ j) = b.repr x j := by
          rw [hr, Finsupp.embDomain_apply_self]
        rw [he] at hh
        exact_mod_cast hh
      have hh := (hb (b.repr x)).2
      rw [b.repr.symm_apply_apply] at hh
      calc
        ‖x‖ ≤ C * ((b.repr x).support.sup (fun j ↦ ‖b.repr x j‖₊) : NNReal) := hh
        _ ≤ C * ((b.repr (f x)).support.sup (fun j ↦ ‖b.repr (f x) j‖₊) : NNReal) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hC0
        _ ≤ C * (c⁻¹ * ‖f x‖) :=
          mul_le_mul_of_nonneg_left ((le_inv_mul_iff₀ hc).2 hl) hC0
        _ = C / c * ‖f x‖ := by ring
    exact ((f.mkContinuous (C / c) hfbound).isUniformEmbedding_of_bound
      (K := ⟨C / c, div_nonneg hC0 hc.le⟩) hanti).isEmbedding

private lemma residual_orthogonal
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    (hu : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (P : Submodule K W) (x : W) (w : P)
    (hmin : ∀ z : P, ‖x - (w : W)‖ ≤ ‖x - (z : W)‖)
    (u : W) (huP : u ∈ P) (a : K) :
    ‖u + a • (x - w)‖ = max ‖u‖ (‖a‖ * ‖x - w‖) := by
  have ha : ‖a‖ * ‖x - w‖ ≤ ‖u + a • (x - w)‖ := by
    by_cases ha : a = 0
    · simp [ha]
    · have h := hmin (w - a⁻¹ • (⟨u, huP⟩ : P))
      have he : a • (x - ((w - a⁻¹ • (⟨u, huP⟩ : P) : P) : W)) =
          u + a • (x - w) := by
        simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_sub, smul_smul,
          mul_inv_cancel₀ ha, one_smul]
        abel
      calc
        ‖a‖ * ‖x - w‖ ≤ ‖a‖ * ‖x - ((w - a⁻¹ • (⟨u, huP⟩ : P) : P) : W)‖ :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = ‖u + a • (x - w)‖ := by rw [← norm_smul, he]
  apply le_antisymm
  · simpa only [norm_smul] using hu u (a • (x - w))
  · apply max_le _ ha
    have h := hu (u + a • (x - w)) (-(a • (x - w)))
    rw [add_neg_cancel_right, norm_neg, norm_smul] at h
    exact h.trans (max_le (le_refl _) ha)

private lemma fin_sup_last {n : ℕ} (f : Fin (n + 1) → NNReal) :
    Finset.univ.sup f = max (Finset.univ.sup (fun i : Fin n ↦ f i.castSucc))
      (f (Fin.last n)) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact le_max_right _ _
    · exact (Finset.le_sup (f := fun j : Fin n ↦ f j.castSucc) (Finset.mem_univ j)).trans
        (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le
      intro i _
      exact Finset.le_sup (Finset.mem_univ i.castSucc)
    · exact Finset.le_sup (Finset.mem_univ (Fin.last n))

private lemma exists_orthogonal_sequence
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    (hu : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (hbest : ∀ (n : ℕ) (f : Fin n → W) (x : W),
      ∃ w : Submodule.span K (Set.range f),
        ∀ z : Submodule.span K (Set.range f), ‖x - (w : W)‖ ≤ ‖x - (z : W)‖)
    (s : ℕ → W) :
    ∃ t : ℕ → W, t 0 = s 0 ∧
      Submodule.span K (Set.range s) ≤ Submodule.span K (Set.range t) ∧
      ∀ (n : ℕ) (a : Fin n → K),
        ‖∑ i, a i • t i‖₊ = Finset.univ.sup (fun i ↦ ‖a i‖₊ * ‖t i‖₊) := by
  classical
  choose w hw using hbest
  let F : (n : ℕ) → Fin n → W := Nat.rec (fun i ↦ Fin.elim0 i)
    (fun n f ↦ Fin.snoc f (s n - (w n f (s n) : W)))
  let t : ℕ → W := fun n ↦ F (n + 1) (Fin.last n)
  have hF (n : ℕ) (i : Fin n) : F n i = t i := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rfl
      · simpa only [F, Fin.snoc_castSucc, Fin.val_castSucc] using ih j
  have horth (n : ℕ) (a : Fin n → K) :
      ‖∑ i, a i • F n i‖₊ = Finset.univ.sup (fun i ↦ ‖a i‖₊ * ‖F n i‖₊) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hm : (∑ i : Fin n, a i.castSucc • F n i) ∈
          Submodule.span K (Set.range (F n)) := by
        apply Submodule.sum_mem
        intro i _
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have he := residual_orthogonal hu _ (s n) (w n (F n) (s n))
        (hw n (F n) (s n)) _ hm (a (Fin.last n))
      rw [fin_sup_last]
      change ‖∑ i, a i • Fin.snoc (α := fun _ ↦ W) (F n) (s n - (w n (F n) (s n) : W)) i‖₊ = _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      apply NNReal.coe_injective
      simp only [NNReal.coe_max, NNReal.coe_mul, coe_nnnorm]
      rw [he]
      have hcast (i : Fin n) : F (n + 1) i.castSucc = F n i := by
        simp only [F, Fin.snoc_castSucc]
      have hlast : F (n + 1) (Fin.last n) = s n - (w n (F n) (s n) : W) := by
        simp only [F, Fin.snoc_last]
      simp only [hcast, hlast]
      exact congrArg (fun r : NNReal ↦ max (r : ℝ)
        (‖a (Fin.last n)‖ * ‖s n - (w n (F n) (s n) : W)‖))
        (ih (fun i ↦ a i.castSucc))
  refine ⟨t, ?_, ?_, fun n a ↦ ?_⟩
  · have hz : (w 0 (F 0) (s 0) : W) = 0 := by
      have h := (w 0 (F 0) (s 0)).property
      simpa using h
    change s 0 - (w 0 (F 0) (s 0) : W) = s 0
    simp [hz]
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    have hwmem : (w n (F n) (s n) : W) ∈ Submodule.span K (Set.range t) := by
      apply (Submodule.span_mono (show Set.range (F n) ⊆ Set.range t from ?_))
        (w n (F n) (s n)).property
      rintro y ⟨i, rfl⟩
      exact ⟨i, hF n i |>.symm⟩
    have ht : t n ∈ Submodule.span K (Set.range t) := Submodule.subset_span ⟨n, rfl⟩
    have htdef : t n = s n - (w n (F n) (s n) : W) := by
      simp only [t, F, Fin.snoc_last]
    rw [htdef] at ht
    have hmem := Submodule.add_mem _ ht hwmem
    rw [sub_add_cancel] at hmem
    exact hmem
  · simpa only [hF] using horth n a

private lemma orthogonal_finset_of_prefix
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    (t : ℕ → W)
    (ht : ∀ (n : ℕ) (a : Fin n → K),
      ‖∑ i, a i • t i‖₊ = Finset.univ.sup (fun i ↦ ‖a i‖₊ * ‖t i‖₊))
    (s : Finset ℕ) (a : ℕ → K) :
    ‖∑ i ∈ s, a i • t i‖₊ = s.sup (fun i ↦ ‖a i‖₊ * ‖t i‖₊) := by
  classical
  let n := s.sup id + 1
  have hs : s ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  let A : ℕ → K := fun i ↦ if i ∈ s then a i else 0
  have he := ht n (fun i ↦ A i)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ A i • t i)] at he
  have hsum : (∑ i ∈ Finset.range n, A i • t i) = ∑ i ∈ s, a i • t i := by
    rw [← Finset.sum_subset hs]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [A, if_pos hi]
    · intro i _ hi
      simp [A, hi]
  rw [hsum, Finset.sup_fin_univ (fun i ↦ ‖A i‖₊ * ‖t i‖₊)] at he
  refine he.trans (le_antisymm ?_ ?_)
  · apply Finset.sup_le
    intro i hi
    by_cases his : i ∈ s
    · simpa only [A, if_pos his] using
        (Finset.le_sup (f := fun i ↦ ‖a i‖₊ * ‖t i‖₊) his)
    · simp [A, his]
  · apply Finset.sup_le
    intro i hi
    simpa only [A, if_pos hi] using
      (Finset.le_sup (f := fun i ↦ ‖A i‖₊ * ‖t i‖₊) (hs hi))

private lemma orthogonal_restrict
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    (t : ℕ → W)
    (ht : ∀ (s : Finset ℕ) (a : ℕ → K),
      ‖∑ i ∈ s, a i • t i‖₊ = s.sup (fun i ↦ ‖a i‖₊ * ‖t i‖₊))
    {ι : Type*} (e : ι ↪ ℕ) (s : Finset ι) (a : ι → K) :
    ‖∑ i ∈ s, a i • t (e i)‖₊ = s.sup (fun i ↦ ‖a i‖₊ * ‖t (e i)‖₊) := by
  classical
  let A : ℕ → K := fun j ↦ if h : ∃ i, e i = j then a h.choose else 0
  have hA (i : ι) : A (e i) = a i := by
    simp only [A, dif_pos (show ∃ j, e j = e i from ⟨i, rfl⟩)]
    congr 1
    exact e.injective (Classical.choose_spec (show ∃ j, e j = e i from ⟨i, rfl⟩))
  have h := ht (s.map e) A
  rw [Finset.sum_map, Finset.sup_map] at h
  change ‖∑ i ∈ s, A (e i) • t (e i)‖₊ =
    s.sup (fun i ↦ ‖A (e i)‖₊ * ‖t (e i)‖₊) at h
  simpa only [hA] using h

private lemma orthogonal_basis
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    {ι : Type*} (f : ι → W) (hfn : ∀ i, f i ≠ 0)
    (hf : ∀ (s : Finset ι) (a : ι → K),
      ‖∑ i ∈ s, a i • f i‖₊ = s.sup (fun i ↦ ‖a i‖₊ * ‖f i‖₊))
    (hspan : Submodule.span K (Set.range f) = ⊤) :
    ∃ b : Module.Basis ι K W, ∀ i, b i = f i := by
  classical
  have hli : LinearIndependent K f := by
    apply linearIndependent_iff'.mpr
    intro s a ha i hi
    have he := hf s a
    rw [ha, nnnorm_zero] at he
    have hterm : ‖a i‖₊ * ‖f i‖₊ ≤ 0 :=
      (Finset.le_sup (f := fun i ↦ ‖a i‖₊ * ‖f i‖₊) hi).trans_eq he.symm
    have hz := le_antisymm hterm (zero_le : (0 : NNReal) ≤ _)
    rcases mul_eq_zero.mp hz with h | h
    · exact nnnorm_eq_zero.mp h
    · exact False.elim (hfn i (nnnorm_eq_zero.mp h))
  exact ⟨Module.Basis.mk hli hspan.ge, fun i ↦ Module.Basis.mk_apply _ _ i⟩

private lemma orthogonal_basis_bounds
    {K : Type*} [NormedField K] {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    {ι : Type*} (b : Module.Basis ι K W) (c C : ℝ) (_hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbn : ∀ i, c ≤ ‖b i‖ ∧ ‖b i‖ ≤ C)
    (hb : ∀ (s : Finset ι) (a : ι → K),
      ‖∑ i ∈ s, a i • b i‖₊ = s.sup (fun i ↦ ‖a i‖₊ * ‖b i‖₊))
    (a : ι →₀ K) :
    c * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) ≤ ‖b.repr.symm a‖ ∧
      ‖b.repr.symm a‖ ≤ C * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) := by
  classical
  have hn : ‖b.repr.symm a‖₊ = a.support.sup (fun i ↦ ‖a i‖₊ * ‖b i‖₊) := by
    simpa only [b.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum] using
      hb a.support a
  constructor
  · rcases a.support.eq_empty_or_nonempty with ha | ha
    · simp [ha]
    · obtain ⟨i, hi, he⟩ := a.support.exists_mem_eq_sup ha (fun i ↦ ‖a i‖₊)
      have hle : ‖a i‖₊ * ‖b i‖₊ ≤ ‖b.repr.symm a‖₊ := by
        rw [hn]
        exact Finset.le_sup (f := fun i ↦ ‖a i‖₊ * ‖b i‖₊) hi
      rw [he]
      calc
        c * ‖a i‖ ≤ ‖a i‖ * ‖b i‖ := by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbn i).1 (norm_nonneg _)
        _ ≤ ‖b.repr.symm a‖ := by exact_mod_cast hle
  · have h : ‖b.repr.symm a‖₊ ≤
        Real.toNNReal C * (a.support.sup (fun i ↦ ‖a i‖₊) : NNReal) := by
      rw [hn]
      apply Finset.sup_le
      intro i hi
      calc
        ‖a i‖₊ * ‖b i‖₊ ≤ ‖a i‖₊ * Real.toNNReal C :=
          mul_le_mul_of_nonneg_left (by
            apply NNReal.coe_le_coe.mp
            simpa only [Real.coe_toNNReal C hC, coe_nnnorm] using (hbn i).2)
            (zero_le : (0 : NNReal) ≤ _)
        _ ≤ Real.toNNReal C * (a.support.sup (fun i ↦ ‖a i‖₊) : NNReal) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Finset.le_sup (f := fun i ↦ ‖a i‖₊) hi)
            (zero_le : (0 : NNReal) ≤ _)
    have hh := NNReal.coe_le_coe.mpr h
    simpa only [NNReal.coe_mul, Real.coe_toNNReal C hC, coe_nnnorm] using hh

private lemma countable_index
    (I : Type*) [Countable I] (i₀ : I) :
    ∃ (J : Set ℕ) (h₀ : 0 ∈ J) (e : J ≃ I),
      (J = Set.univ ∨ ∃ d : ℕ, 1 ≤ d ∧ J = Set.Iio d) ∧ e ⟨0, h₀⟩ = i₀ := by
  classical
  let : Nonempty I := ⟨i₀⟩
  have adjust (J : Set ℕ) (h₀ : 0 ∈ J) (e : J ≃ I) :
      ∃ e' : J ≃ I, e' ⟨0, h₀⟩ = i₀ := by
    exact ⟨e.trans (Equiv.swap (e ⟨0, h₀⟩) i₀), by simp⟩
  cases finite_or_infinite I with
  | inl h =>
    let := Fintype.ofFinite I
    let d := Fintype.card I
    have hd : 0 < d := Fintype.card_pos
    let e : Set.Iio d ≃ I :=
      (Equiv.refl (Set.Iio d)).trans
        (show Set.Iio d ≃ Fin d from
          ⟨fun i ↦ ⟨i, i.property⟩, fun i ↦ ⟨i, i.isLt⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩)
        |>.trans (Fintype.equivFin I).symm
    obtain ⟨e', he'⟩ := adjust (Set.Iio d) hd e
    exact ⟨Set.Iio d, hd, e', Or.inr ⟨d, hd, rfl⟩, he'⟩
  | inr h =>
    let := h
    let := nonempty_denumerable I |>.some
    let e : (Set.univ : Set ℕ) ≃ I :=
      (Equiv.Set.univ ℕ).trans (Denumerable.eqv I).symm
    obtain ⟨e', he'⟩ := adjust Set.univ (Set.mem_univ 0) e
    exact ⟨Set.univ, Set.mem_univ 0, e', Or.inl rfl, he'⟩

open Classical in
/-- A countably generated ultrametric normed space has uniformly bounded algebraic
coordinates with any prescribed nonzero first basis vector.

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent auxiliary for the geometric norm projection; exact reference WANTED
(blueprint: lem-sfb-countable-normed-orthogonal-basis).

Proof: Prepend `v₀` to a spanning sequence. Starting with `v₀`, discard vectors already
in the retained finite span. Otherwise apply `lem-sfb-finite-ultrametric-best-approximation`
to subtract a nearest point in that span; `lem-sfb-ultrametric-orthogonal-extension`
shows that the resulting nonzero residual extends the orthogonal family and preserves
its span together with the next sequence vector. Each finite subfamily occurs in a
finite stage, so the retained family is independent and orthogonal. Every sequence
vector belongs to a finite-stage span, so the family is an algebraic basis indexed by
a nonempty initial segment of the naturals or all the naturals.

Put `q = |ℓ|⁻¹ > 1`. Leave the first vector fixed and multiply each other vector by
an integer power of `ℓ` so its norm lies in `[1,q)`. This preserves orthogonality and
the algebraic basis property. The exact orthogonal finite-sum formula implies the
two bounds with `c = min ‖v₀‖ 1` and `C = max ‖v₀‖ q`, including the empty support.
The lower bound controls every coordinate; the upper bound then controls every subset
projection and every injective basis relabeling by `C/c`. The lower bound for such a
relabeling also controls its inverse on the coordinate subspace, so it is an embedding.
All expansions are finite, and completeness of `V` is never used.

`J` is an initial segment or all of `ℕ`. `Finset.sup` in `ℝ≥0` gives zero on empty
support. The final embedding clause states continuity of each basis injection and of
its inverse onto its image, which is the span of the selected basis subset.
-/
theorem exists_countable_ultrametric_basis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (V : Type v) [NormedAddCommGroup V]
    (h_ultra : ∀ x y : V, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (v₀ : V) (hv₀ : v₀ ≠ 0) :
    letI := spectralNorm.nontriviallyNormedField (Padic l) E
    ∀ [NormedSpace E V],
      (∃ s : ℕ → V, Submodule.span E (Set.range s) = ⊤) →
      ∃ (J : Set ℕ) (h₀ : 0 ∈ J) (b : Module.Basis J E V) (c C : ℝ),
        (J = Set.univ ∨ ∃ d : ℕ, 1 ≤ d ∧ J = Set.Iio d) ∧
        b ⟨0, h₀⟩ = v₀ ∧ 0 < c ∧ c ≤ C ∧
        (∀ a : J →₀ E,
          c * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ) ≤ ‖b.repr.symm a‖ ∧
          ‖b.repr.symm a‖ ≤ C * ((a.support.sup (fun j ↦ ‖a j‖₊) : NNReal) : ℝ)) ∧
        (∀ j : J, Continuous (b.coord j)) ∧
        (∀ S : Set J, Continuous (b.constr E (fun j ↦ if j ∈ S then b j else 0))) ∧
        (∀ σ : J ↪ J, Topology.IsEmbedding (b.constr E (fun j ↦ b (σ j)))) := by
  classical
  let := spectralNorm.nontriviallyNormedField (Padic l) E
  intro _ hs
  obtain ⟨s, hs⟩ := hs
  let s' : ℕ → V := fun n ↦ Nat.casesOn n v₀ s
  have hs' : Submodule.span E (Set.range s') = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    rintro x ⟨n, rfl⟩
    exact ⟨n + 1, rfl⟩
  have hbest (n : ℕ) (f : Fin n → V) (x : V) :
      ∃ w : Submodule.span E (Set.range f),
        ∀ z : Submodule.span E (Set.range f), ‖x - (w : V)‖ ≤ ‖x - (z : V)‖ := by
    let := FiniteDimensional.span_of_finite E (Set.finite_range f)
    obtain ⟨w, hw⟩ := (exists_finite_ultrametric_best_approximation l E V
      (fun a z ↦ by exact norm_smul a z) h_ultra (Submodule.span E (Set.range f)) x).1
    refine ⟨w, fun z ↦ ?_⟩
    rw [hw]
    exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ z
  obtain ⟨t, ht0, htspan, htorth⟩ := exists_orthogonal_sequence h_ultra hbest s'
  have htorth' := orthogonal_finset_of_prefix t htorth
  have ht0' : t 0 = v₀ := ht0
  let I : Set ℕ := {i | t i ≠ 0}
  have hi₀ : 0 ∈ I := by simpa only [I, Set.mem_ofPred_eq, ht0'] using hv₀
  have hspan : Submodule.span E (Set.range (fun i : I ↦ t i)) = ⊤ := by
    have htfull : Submodule.span E (Set.range t) = ⊤ := by
      apply top_unique
      rw [← hs']
      exact htspan
    rw [eq_top_iff, ← htfull]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : t i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨bI, hbI⟩ := orthogonal_basis (fun i : I ↦ t i) (fun i ↦ i.property)
    (orthogonal_restrict t htorth' (Function.Embedding.subtype I)) hspan
  obtain ⟨J, h₀, e, hJ, he₀⟩ := countable_index I ⟨0, hi₀⟩
  let b := bI.reindex e.symm
  have hb (i : J) : b i = t (e i) := by
    simp only [b, Module.Basis.reindex_apply, Equiv.symm_symm, hbI]
  have hb₀ : b ⟨0, h₀⟩ = v₀ := by rw [hb, he₀]; exact ht0'
  have hborth (S : Finset J) (a : J → E) :
      ‖∑ i ∈ S, a i • b i‖₊ = S.sup (fun i ↦ ‖a i‖₊ * ‖b i‖₊) := by
    have h := orthogonal_restrict t htorth'
      (e.toEmbedding.trans (Function.Embedding.subtype I)) S a
    change ‖∑ i ∈ S, a i • t (e i)‖₊ =
      S.sup (fun i ↦ ‖a i‖₊ * ‖t (e i)‖₊) at h
    simpa only [hb] using h
  obtain ⟨q, hq⟩ := NormedField.exists_one_lt_norm E
  have hq0 : 0 < ‖q‖ := lt_trans zero_lt_one hq
  have hrescale (j : J) : ∃ d : E, d ≠ 0 ∧
      (j = ⟨0, h₀⟩ → d = 1) ∧
      (j ≠ ⟨0, h₀⟩ → 1 ≤ ‖d • b j‖ ∧ ‖d • b j‖ ≤ ‖q‖) := by
    by_cases hj : j = ⟨0, h₀⟩
    · exact ⟨1, one_ne_zero, fun _ ↦ rfl, fun h ↦ False.elim (h hj)⟩
    · obtain ⟨d, hd, hdlt, hdle, -⟩ := rescale_to_shell hq hq0 (b.ne_zero j)
      refine ⟨d, hd, fun h ↦ False.elim (hj h), fun _ ↦ ⟨?_, hdlt.le⟩⟩
      simpa only [div_self hq0.ne'] using hdle
  choose d hd hd₀ hdn using hrescale
  let B := b.unitsSMul (fun j ↦ Units.mk0 (d j) (hd j))
  have hB (j : J) : B j = d j • b j := by
    simp only [B, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hB₀ : B ⟨0, h₀⟩ = v₀ := by rw [hB, hd₀ _ rfl, one_smul, hb₀]
  let c := min ‖v₀‖ 1
  let C := max ‖v₀‖ ‖q‖
  have hc : 0 < c := lt_min (norm_pos_iff.mpr hv₀) zero_lt_one
  have hcC : c ≤ C := (min_le_left _ _).trans (le_max_left _ _)
  have hBn (j : J) : c ≤ ‖B j‖ ∧ ‖B j‖ ≤ C := by
    by_cases hj : j = ⟨0, h₀⟩
    · subst j
      rw [hB₀]
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · have h := hdn j hj
      rw [← hB] at h
      exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩
  have hBorth (S : Finset J) (a : J → E) :
      ‖∑ i ∈ S, a i • B i‖₊ = S.sup (fun i ↦ ‖a i‖₊ * ‖B i‖₊) := by
    simpa only [hB, smul_smul, nnnorm_smul, nnnorm_mul, ← mul_assoc] using
      hborth S (fun i ↦ a i * d i)
  have hbounds := orthogonal_basis_bounds B c C hc.le (hc.le.trans hcC) hBn hBorth
  obtain ⟨hcoord, hproj, hemb⟩ := bounded_basis_topology h_ultra B c C hc hcC hbounds
  exact ⟨J, h₀, B, c, C, hJ, hB₀, hc, hcC, hbounds, hcoord, hproj, hemb⟩

end Padic
