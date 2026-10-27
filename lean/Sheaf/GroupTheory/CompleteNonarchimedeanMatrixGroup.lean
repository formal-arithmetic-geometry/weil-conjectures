/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Complete nonarchimedean matrix groups

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 7.1.5,
pp. 63--64, and the agent matrix-group argument recorded in the blueprint node.
(blueprint: lem-sfb-complete-nonarchimedean-matrix-group)
-/

@[expose] public section

set_option autoImplicit false
universe u v

open Filter Topology UniformSpace

namespace Matrix.GeneralLinearGroup

private theorem max_matrix_mul_le {F : Type u} [NormedField F]
    (hF : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (n : ℕ)
    (a b : Matrix (Fin n) (Fin n) F) :
    ‖fun i j ↦ (a * b) i j‖ ≤ ‖fun i j ↦ a i j‖ * ‖fun i j ↦ b i j‖ := by
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hF
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro j
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro k _
  exact (norm_mul_le _ _).trans (mul_le_mul
    ((norm_le_pi_norm (a i) k).trans (norm_le_pi_norm a i))
    ((norm_le_pi_norm (b k) j).trans (norm_le_pi_norm b k))
    (norm_nonneg _) (norm_nonneg _))

@[instance_reducible]
private noncomputable def max_matrix_normedRing {F : Type u} [NormedField F]
    (hF : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (n : ℕ) :
    NormedRing (Matrix (Fin n) (Fin n) F) :=
  { Matrix.normedAddCommGroup, Matrix.instRing with
    norm_mul_le := max_matrix_mul_le hF n }

private theorem completion_nonarchimedean (A : Type u) [NormedField A]
    (hA : ∀ x y : A, ‖x + y‖ ≤ max ‖x‖ ‖y‖) :
    ∀ x y : Completion A, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  intro x y
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_le (continuous_norm.comp (continuous_fst.add continuous_snd))
      ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd))
  · intro a b
    simpa only [← Completion.coe_add, Completion.norm_coe] using hA a b

private theorem units_values_cauchy {R : Type u} [NormedRing R] {J : Type v}
    (f : Filter J) [NeBot f] (g : J → Rˣ)
    (hg : Tendsto (fun p : J × J ↦ (g p.1)⁻¹ * g p.2) (f ×ˢ f) (𝓝 1)) :
    Cauchy (Filter.map (fun j ↦ (g j : R)) f) := by
  have he : ∀ ε > 0, ∀ᶠ p : J × J in f ×ˢ f,
      ‖(↑((g p.1)⁻¹ * g p.2) : R) - 1‖ < ε := by
    intro ε hε
    have hc := (Units.continuous_val.tendsto 1).comp hg
    exact (tendsto_order.1 ((hc.sub tendsto_const_nhds).norm)).2 ε (by simpa using hε)
  obtain ⟨p, hp, q, hq, hpq⟩ := eventually_prod_iff.mp (he 1 zero_lt_one)
  obtain ⟨k, hk⟩ := hp.exists
  let M := ‖(g k : R)‖ * (‖(1 : R)‖ + 1) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ᶠ j in f, ‖(g j : R)‖ ≤ M := by
    filter_upwards [hq] with j hj
    have hr : ‖(↑((g k)⁻¹ * g j) : R)‖ ≤ ‖(1 : R)‖ + 1 := by
      have ht := norm_add_le (↑((g k)⁻¹ * g j) - 1 : R) (1 : R)
      rw [sub_add_cancel] at ht
      linarith [hpq hk hj]
    calc
      ‖(g j : R)‖ = ‖(g k : R) * ↑((g k)⁻¹ * g j)‖ := by simp
      _ ≤ ‖(g k : R)‖ * ‖(↑((g k)⁻¹ * g j) : R)‖ := norm_mul_le _ _
      _ ≤ ‖(g k : R)‖ * (‖(1 : R)‖ + 1) := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ ≤ M := by dsimp [M]; linarith
  rw [cauchy_map_iff']
  apply Metric.uniformity_basis_dist.tendsto_right_iff.mpr
  intro ε hε
  filter_upwards [he (ε / M) (div_pos hε hM), tendsto_fst.eventually hb] with p hp hpM
  rw [dist_eq_norm, norm_sub_rev]
  have hid' : (g p.2 : R) - (g p.1 : R) =
      (g p.1 : R) * (↑((g p.1)⁻¹ * g p.2) - 1) := by
    simp [mul_sub]
  rw [hid']
  calc
    _ ≤ ‖(g p.1 : R)‖ * ‖(↑((g p.1)⁻¹ * g p.2) : R) - 1‖ := norm_mul_le _ _
    _ ≤ M * ‖(↑((g p.1)⁻¹ * g p.2) : R) - 1‖ :=
      mul_le_mul_of_nonneg_right hpM (norm_nonneg _)
    _ < M * (ε / M) := mul_lt_mul_of_pos_left hp hM
    _ = ε := mul_div_cancel₀ ε hM.ne'

private theorem units_inv_sub_one_le {R : Type u} [NormedRing R] [IsUltrametricDist R]
    (h1 : ‖(1 : R)‖ ≤ 1) (g : Rˣ) (hg : ‖(g : R) - 1‖ < 1) :
    ‖(↑g⁻¹ : R) - 1‖ ≤ ‖(g : R) - 1‖ := by
  have he : (↑g⁻¹ : R) - 1 = -(↑g⁻¹ * ((g : R) - 1)) := by simp [mul_sub]
  have hd : ‖(↑g⁻¹ : R) - 1‖ ≤ ‖(↑g⁻¹ : R)‖ * ‖(g : R) - 1‖ := by
    rw [he, norm_neg]
    exact norm_mul_le _ _
  have hb : ‖(↑g⁻¹ : R)‖ ≤ 1 := by
    by_contra! hn
    have hh := IsUltrametricDist.norm_add_le_max ((↑g⁻¹ : R) - 1) (1 : R)
    rw [sub_add_cancel] at hh
    have hh' := hh.trans (max_le_max hd h1)
    have hm : ‖(↑g⁻¹ : R)‖ * ‖(g : R) - 1‖ < ‖(↑g⁻¹ : R)‖ := by
      simpa using mul_lt_mul_of_pos_left hg (lt_trans zero_lt_one hn)
    exact (not_lt_of_ge hh') (max_lt hm hn)
  exact hd.trans (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg ((g : R) - 1)))

private theorem units_cauchy_converges {R : Type u} [NormedRing R] [CompleteSpace R]
    {J : Type v} (f : Filter J) [NeBot f] (g : J → Rˣ)
    (hL : Tendsto (fun p : J × J ↦ (g p.1)⁻¹ * g p.2) (f ×ˢ f) (𝓝 1))
    (hR : Tendsto (fun p : J × J ↦ g p.1 * (g p.2)⁻¹) (f ×ˢ f) (𝓝 1)) :
    ∃ l : Rˣ, Tendsto g f (𝓝 l) := by
  obtain ⟨a, ha⟩ := cauchy_map_iff_exists_tendsto.mp (units_values_cauchy f g hL)
  obtain ⟨b, hb⟩ := cauchy_map_iff_exists_tendsto.mp
    (units_values_cauchy f (fun j ↦ (g j)⁻¹) (by simpa using hR))
  have hab : a * b = 1 := by
    have ht := ha.mul hb
    simp only [Units.mul_inv] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hba : b * a = 1 := by
    have ht := hb.mul ha
    simp only [Units.inv_mul] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let l : Rˣ := ⟨a, b, hab, hba⟩
  refine ⟨l, ?_⟩
  apply Units.isInducing_embedProduct.tendsto_nhds_iff.mpr
  change Tendsto (fun j ↦ ((g j : R), MulOpposite.op (↑(g j)⁻¹ : R))) f
    (𝓝 (a, MulOpposite.op b))
  rw [nhds_prod_eq]
  exact ha.prodMk (MulOpposite.opHomeomorph.continuous.tendsto b |>.comp hb)

private theorem units_two_sided_complete {R : Type u} [NormedRing R] [CompleteSpace R] :
    @CompleteSpace Rˣ
      (IsTopologicalGroup.leftUniformSpace Rˣ ⊓
        IsTopologicalGroup.rightUniformSpace Rˣ) := by
  let uL := IsTopologicalGroup.leftUniformSpace Rˣ
  let uR := IsTopologicalGroup.rightUniformSpace Rˣ
  let u := uL ⊓ uR
  have htop : u.toTopologicalSpace = (inferInstance : TopologicalSpace Rˣ) := by
    exact inf_idem _
  refine ⟨fun {f} hf ↦ ?_⟩
  have : NeBot f := hf.1
  have hLf : f ×ˢ f ≤ uL.uniformity := hf.2.trans inf_le_left
  have hRf : f ×ˢ f ≤ uR.uniformity := hf.2.trans inf_le_right
  change f ×ˢ f ≤ Filter.comap (fun p : Rˣ × Rˣ ↦ p.1⁻¹ * p.2) (𝓝 1) at hLf
  change f ×ˢ f ≤ Filter.comap (fun p : Rˣ × Rˣ ↦ p.2 * p.1⁻¹) (𝓝 1) at hRf
  have hL : Tendsto (fun p : Rˣ × Rˣ ↦ p.1⁻¹ * p.2) (f ×ˢ f) (𝓝 1) :=
    Filter.map_le_iff_le_comap.mpr hLf
  have hR : Tendsto (fun p : Rˣ × Rˣ ↦ p.1 * p.2⁻¹) (f ×ˢ f) (𝓝 1) :=
    (show Tendsto (fun p : Rˣ × Rˣ ↦ p.2 * p.1⁻¹) (f ×ˢ f) (𝓝 1) from
      Filter.map_le_iff_le_comap.mpr hRf).comp (tendsto_snd.prodMk tendsto_fst)
  obtain ⟨l, hl⟩ := units_cauchy_converges f id hL hR
  refine ⟨l, ?_⟩
  change f ≤ @nhds Rˣ u.toTopologicalSpace l
  rw [htop]
  exact hl

/-- Over the normed-field completion of a nonarchimedean normed field, the general linear
 group has the matrix subspace topology, small congruence open subgroups, geometric inverses,
 and completeness for the infimum of the left and right group uniformities. The nested Pi
 norm is precisely the maximum of the entry norms, with value zero for an empty matrix.

Source: Bhatt--Scholze, Proposition 7.1.5, pp. 63--64; agent matrix-group argument.
(blueprint: lem-sfb-complete-nonarchimedean-matrix-group)

Proof:
1. Use lem-sfb-normed-field-completion for the complete normed field and its dense isometric
   inclusion. Approximate two elements by elements of the original field and pass the
   nonarchimedean norm inequality to the limit.
2. For zero size all matrices and all group elements coincide. Otherwise the maximum-entry
   norm N satisfies N(C+D) <= max(N(C),N(D)), N(-C)=N(C), N(CD) <= N(C)N(D), and N(I)=1.
   Bound each finite sum in a product entry by its largest summand.
3. Maximum-norm balls give the finite product topology. Matrix addition and multiplication
   are continuous entrywise, and the matrix space and its invertible subspace are Hausdorff.
4. For q=N(B)<1, the finite geometric sums have tails bounded by q^(k+1). Apply
   lem-wf-geometric-decay and lem-sfb-complete-field-cauchy-filter-limit coordinatewise.
   The finite geometric identities give both inverse equations for their limit.
5. The same estimates give N((I+B)^(-1)-I) <= q and N((I+B)^(-1)) <= 1. Treat B=0 directly.
6. The formula (I+B)(I+C)=I+(B+C+BC) proves closure of each congruence ball under products;
   step 5 proves inverse closure. Strict coordinate inequalities make it open. Every identity
   neighborhood contains a ball with radius strictly between zero and min(1,epsilon).
7. At an invertible g write x=g(I+D) with D=g^(-1)(x-g). Step 5 bounds
   N(x^(-1)-g^(-1)) by N(g^(-1))^2 N(x-g), proving continuity of inversion and hence the
   agreement of the units topology with the matrix subspace topology.
8. For a two-sided Cauchy net choose a tail whose relative differences lie in one small
   congruence subgroup. Fixing one index bounds both the matrices and their inverses by M.
   The identities g_j-g_i=g_i(g_i^(-1)g_j-I) and
   g_i^(-1)-g_j^(-1)=g_i^(-1)(I-g_i g_j^(-1)) turn the two relative Cauchy conditions
   into coordinatewise additive Cauchy conditions.
9. Apply lem-sfb-complete-field-cauchy-filter-limit to the proper tail filter in each
   coordinate, for both nets. Continuity gives ab=ba=I, so a is invertible with inverse b.
   The original net therefore converges in the matrix subspace topology. This is completeness
   for the two-sided uniformity.
-/
theorem complete_nonarchimedean_matrix_group
    (A : Type u) [NormedField A]
    (hA : ∀ x y : A, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (n : ℕ) :
    (∀ x y : Completion A, ‖x + y‖ ≤ max ‖x‖ ‖y‖) ∧
    IsInducing (fun g : GeneralLinearGroup (Fin n) (Completion A) =>
      (g : Matrix (Fin n) (Fin n) (Completion A))) ∧
    T2Space (GeneralLinearGroup (Fin n) (Completion A)) ∧
    IsTopologicalGroup (GeneralLinearGroup (Fin n) (Completion A)) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      ∃ U : OpenSubgroup (GeneralLinearGroup (Fin n) (Completion A)),
        ∀ g : GeneralLinearGroup (Fin n) (Completion A),
          g ∈ U ↔ ‖fun i j : Fin n => g i j - (1 : Matrix (Fin n) (Fin n) (Completion A)) i j‖
            < r) ∧
    (∀ V ∈ 𝓝 (1 : GeneralLinearGroup (Fin n) (Completion A)),
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        {g : GeneralLinearGroup (Fin n) (Completion A) |
          ‖fun i j : Fin n => g i j - (1 : Matrix (Fin n) (Fin n) (Completion A)) i j‖ < r}
          ⊆ V) ∧
    (∀ B : Matrix (Fin n) (Fin n) (Completion A), ‖fun i j => B i j‖ < 1 →
      IsUnit (1 + B) ∧ HasSum (fun m : ℕ => (-B) ^ m) (1 + B)⁻¹) ∧
    (∀ (J : Type v) [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
        (g : J → GeneralLinearGroup (Fin n) (Completion A)),
      Tendsto (fun p : J × J => (g p.1)⁻¹ * g p.2) (atTop ×ˢ atTop) (𝓝 1) →
      Tendsto (fun p : J × J => g p.1 * (g p.2)⁻¹) (atTop ×ˢ atTop) (𝓝 1) →
      ∃ (a b : Matrix (Fin n) (Fin n) (Completion A))
          (l : GeneralLinearGroup (Fin n) (Completion A)),
        (∀ i j, Tendsto (fun k => g k i j) atTop (𝓝 (a i j))) ∧
        (∀ i j, Tendsto (fun k => ((g k)⁻¹) i j) atTop (𝓝 (b i j))) ∧
        a * b = 1 ∧ b * a = 1 ∧
        (l : Matrix (Fin n) (Fin n) (Completion A)) = a ∧
        ((l⁻¹ : GeneralLinearGroup (Fin n) (Completion A)) :
          Matrix (Fin n) (Fin n) (Completion A)) = b ∧
        Tendsto g atTop (𝓝 l)) ∧
    @CompleteSpace (GeneralLinearGroup (Fin n) (Completion A))
      (IsTopologicalGroup.leftUniformSpace (GeneralLinearGroup (Fin n) (Completion A)) ⊓
        IsTopologicalGroup.rightUniformSpace (GeneralLinearGroup (Fin n) (Completion A))) := by
  have hF := completion_nonarchimedean A hA
  let := max_matrix_normedRing hF n
  let : CompleteSpace (Matrix (Fin n) (Fin n) (Completion A)) :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → Completion A))
  let : IsUltrametricDist (Completion A) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hF
  let : IsUltrametricDist (Matrix (Fin n) (Fin n) (Completion A)) :=
    inferInstanceAs (IsUltrametricDist (Fin n → Fin n → Completion A))
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) (Completion A))‖ ≤ 1 := by
    apply Matrix.norm_le_iff zero_le_one |>.mpr
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hi : IsInducing (fun g : GeneralLinearGroup (Fin n) (Completion A) ↦
      (g : Matrix (Fin n) (Fin n) (Completion A))) :=
    Units.isOpenEmbedding_val.isEmbedding.isInducing
  refine ⟨hF, hi, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr hr1
    let U : OpenSubgroup (GeneralLinearGroup (Fin n) (Completion A)) :=
      { carrier := {g | ‖(g : Matrix (Fin n) (Fin n) (Completion A)) - 1‖ < r}
        one_mem' := by simpa using hr
        mul_mem' := by
          intro g h hg hh
          change ‖(↑(g * h) : Matrix (Fin n) (Fin n) (Completion A)) - 1‖ < r
          have hid : (↑(g * h) : Matrix (Fin n) (Fin n) (Completion A)) - 1 =
              ((g : Matrix (Fin n) (Fin n) (Completion A)) - 1) +
              ((h : Matrix (Fin n) (Fin n) (Completion A)) - 1) +
              ((g : Matrix (Fin n) (Fin n) (Completion A)) - 1) *
              ((h : Matrix (Fin n) (Fin n) (Completion A)) - 1) := by
            simp [sub_mul, mul_sub, Units.val_mul]
            abel
          rw [hid]
          apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          apply max_lt
          · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hg hh)
          · apply (norm_mul_le _ _).trans_lt
            exact (mul_le_mul_of_nonneg_right (lt_trans hg hr1).le
              (norm_nonneg _)).trans_lt (by simpa using hh)
        inv_mem' := by
          intro g hg
          exact (units_inv_sub_one_le h1 g (lt_trans hg hr1)).trans_lt hg
        isOpen' := isOpen_lt
          ((Units.continuous_val.sub continuous_const).norm) continuous_const }
    exact ⟨U, fun _ ↦ Iff.rfl⟩
  · intro V hV
    rw [hi.nhds_eq_comap] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
    obtain ⟨r, hr, hrmin⟩ := exists_between (lt_min hε zero_lt_one)
    refine ⟨r, hr, (lt_min_iff.mp hrmin).2, ?_⟩
    intro g hg
    apply hWV
    apply hεW
    change dist (g : Matrix (Fin n) (Fin n) (Completion A)) 1 < ε
    rw [dist_eq_norm]
    exact lt_trans hg (lt_min_iff.mp hrmin).1
  · intro B hB
    constructor
    · simpa only [sub_neg_eq_add] using
        (isUnit_one_sub_of_norm_lt_one (x := -B) (by simpa using hB))
    · simpa only [sub_neg_eq_add, Matrix.nonsing_inv_eq_ringInverse] using
        (hasSum_geom_series_inverse (-B) (by simpa using hB))
  · intro J _ _ _ g hL hR
    obtain ⟨l, hl⟩ := units_cauchy_converges atTop g hL hR
    refine ⟨(l : Matrix (Fin n) (Fin n) (Completion A)),
      (↑l⁻¹ : Matrix (Fin n) (Fin n) (Completion A)), l, ?_, ?_,
      l.val_inv, l.inv_val, rfl, rfl, hl⟩
    · intro i j
      exact (continuous_apply_apply i j).tendsto _ |>.comp
        ((Units.continuous_val.tendsto l).comp hl)
    · intro i j
      exact (continuous_apply_apply i j).tendsto _ |>.comp
        ((Units.continuous_coe_inv.tendsto l).comp hl)
  · exact units_two_sided_complete

end Matrix.GeneralLinearGroup
