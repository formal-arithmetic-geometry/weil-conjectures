/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Homogeneous residual and normalized right-coset averaging

Source: latest blueprint, six-functors direct-images proof, paragraph (3),
agent-written scalar tame-kernel auxiliary expansion, retained steps 10--12.
(blueprint: lem-sfb-coset-averaged-homogeneous-residual).

Tuple length k represents degree k-1, including the empty tuple at k=0.
The positive degree in the statement is n+1. Families A and Q are padded outside
lengths 0 through n+2; no condition is imposed on these unused components.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace ContinuousCohomology.CosetResidual

/-- Free integer tuple chains, with the canonical single-vector basis of
`def-weil-pbc-free-module`; length zero is the unique empty tuple.
Source: direct-images (3), scalar auxiliary expansion
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
abbrev Chain (G : Type u) (k : ℕ) := (Fin k → G) →₀ ℤ

/-- Alternating deletion, including the singleton augmentation.
Source: direct-images (3), scalar auxiliary expansion
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def boundary (G : Type u) (k : ℕ) : Chain G (k + 1) →ₗ[ℤ] Chain G k :=
  Finsupp.linearCombination ℤ (fun x ↦
    ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • Finsupp.single (x ∘ i.succAbove) 1)

/-- Diagonal left translation extended to chains.
Source: direct-images (3), scalar auxiliary expansion
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def translate {G : Type u} [Group G] (k : ℕ) (g : G) :
    Chain G k →ₗ[ℤ] Chain G k :=
  Finsupp.lmapDomain ℤ ℤ (fun x i ↦ g * x i)

/-- Diagonal invariance for the trivial coefficient action.
Source: direct-images (3), scalar auxiliary expansion
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
def Invariant {G : Type u} [Group G] {V : Type v} (H : Subgroup G)
    {k : ℕ} (F : (Fin k → G) → V) : Prop :=
  ∀ (h : H) (x : Fin k → G), F (fun i ↦ (h : G) * x i) = F x

/-- The additive extension of a function to the specified free tuple group.
Source: direct-images (3), scalar auxiliary expansion, step 1
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def evaluate {G : Type u} {V : Type v} [AddCommGroup V] {k : ℕ}
    (F : (Fin k → G) → V) : Chain G k →ₗ[ℤ] V :=
  Finsupp.linearCombination ℤ F

/-- Homogeneous alternating-deletion differential on functions of tuple length k.
Source: direct-images (3), scalar auxiliary expansion, step 2
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def delta {G : Type u} {V : Type v} [AddCommGroup V] {k : ℕ}
    (F : (Fin k → G) → V) : (Fin (k + 1) → G) → V :=
  fun x ↦ ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • F (x ∘ i.succAbove)

/-- Normalized averaging over the given finite transversal. Its denominator is
its cardinality, equal to the subgroup index for a right transversal.
Source: direct-images (3), scalar auxiliary expansion, steps 3--5
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def average {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V]
    (D : Finset G) {k : ℕ} (F : (Fin k → G) → V) : (Fin k → G) → V :=
  fun x ↦ (D.card : ℚ_[l])⁻¹ • ∑ s ∈ D, F (fun i ↦ s * x i)

/-- Evaluation of a specified chain operator, giving U for Q and W for A.
Source: direct-images (3), scalar auxiliary expansion, step 6
(blueprint: lem-sfb-coset-averaged-homogeneous-residual). -/
noncomputable def pull {G : Type u} {V : Type v} [AddCommGroup V] {k r : ℕ}
    (T : Chain G k →ₗ[ℤ] Chain G r) (F : (Fin r → G) → V) : (Fin k → G) → V :=
  fun x ↦ evaluate F (T (Finsupp.single x 1))

private theorem evaluate_single {G : Type u} {V : Type v} [AddCommGroup V]
    {k : ℕ} (F : (Fin k → G) → V) (x : Fin k → G) :
    evaluate F (Finsupp.single x 1) = F x := by
  simp [evaluate]

private theorem evaluate_boundary {G : Type u} {V : Type v} [AddCommGroup V]
    {k : ℕ} (F : (Fin k → G) → V) (z : Chain G (k + 1)) :
    evaluate F (boundary G k z) = evaluate (delta F) z := by
  have he : (evaluate F).comp (boundary G k) = evaluate (delta F) := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp [boundary, evaluate, delta]
  exact LinearMap.congr_fun he z

private theorem evaluate_translate {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] {k : ℕ} (H : Subgroup G) (F : (Fin k → G) → V)
    (hF : Invariant H F) (h : H) (z : Chain G k) :
    evaluate F (translate k (h : G) z) = evaluate F z := by
  have he : (evaluate F).comp (translate k (h : G)) = evaluate F := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simpa [evaluate, translate] using hF h x
  exact LinearMap.congr_fun he z

private theorem delta_add {G : Type u} {V : Type v} [AddCommGroup V] {k : ℕ}
    (F F' : (Fin k → G) → V) : delta (F + F') = delta F + delta F' := by
  ext x
  simp [delta, smul_add, Finset.sum_add_distrib]

private theorem delta_squared {G : Type u} {V : Type v} [AddCommGroup V]
    (k : ℕ) (F : (Fin (k + 1) → G) → V) : delta (delta F) = 0 := by
  classical
  ext x
  simp only [delta, Finset.smul_sum, smul_smul, ← Finset.sum_product']
  let τ : Fin (k + 3) × Fin (k + 2) → Fin (k + 3) × Fin (k + 2) :=
    fun p ↦ (p.1.succAbove p.2, p.2.predAbove p.1)
  apply Finset.sum_ninvolution τ
  · rintro ⟨i, j⟩
    have ht : (x ∘ (i.succAbove j).succAbove) ∘ (j.predAbove i).succAbove =
        (x ∘ i.succAbove) ∘ j.succAbove := by
      funext a
      simp only [Function.comp_apply, Fin.succAbove_succAbove_succAbove_predAbove]
    dsimp [τ]
    rw [ht, ← add_smul]
    suffices hs : (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val +
        (-1 : ℤ) ^ (i.succAbove j).val * (-1 : ℤ) ^ (j.predAbove i).val = 0 by
      rw [hs, zero_smul]
    rcases lt_or_ge j.castSucc i with hij | hij
    · rw [Fin.succAbove_of_castSucc_lt _ _ hij,
        Fin.predAbove_of_castSucc_lt _ _ hij]
      have hi : i.val = (i.pred (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij))).val + 1 :=
        by
          simp only [Fin.val_pred]
          have hj := hij
          simp only [Fin.lt_def, Fin.val_castSucc] at hj
          omega
      rw [hi, pow_succ]
      simp only [Fin.val_castSucc]
      ring
    · rw [Fin.succAbove_of_le_castSucc _ _ hij,
        Fin.predAbove_of_le_castSucc _ _ hij]
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [pow_succ]
      ring
  · rintro ⟨i, j⟩ _ he
    exact Fin.succAbove_ne i j (congrArg Prod.fst he)
  · intro p
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j)
      (Fin.predAbove_predAbove_succAbove i j)

private theorem average_add {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (D : Finset G)
    {k : ℕ} (F F' : (Fin k → G) → V) :
    average (l := l) D (F + F') = average (l := l) D F + average (l := l) D F' := by
  ext x
  simp [average, Finset.sum_add_distrib, smul_add]

private theorem average_smul {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (D : Finset G)
    {k : ℕ} (c : ℚ_[l]) (F : (Fin k → G) → V) :
    average (l := l) D (c • F) = c • average (l := l) D F := by
  ext x
  simp only [average, Pi.smul_apply, ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem average_zero {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (D : Finset G) {k : ℕ} :
    average (l := l) D (0 : (Fin k → G) → V) = 0 := by
  ext x
  simp [average]

private theorem delta_average {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (D : Finset G)
    {k : ℕ} (F : (Fin k → G) → V) :
    delta (average (l := l) D F) = average (l := l) D (delta F) := by
  ext x
  simp only [delta, average, Finset.smul_sum]
  simp_rw [smul_comm ((-1 : ℤ) ^ _)]
  rw [Finset.sum_comm]
  rfl

private theorem average_fixed {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (H : Subgroup G) (D : Finset G)
    (hD : Subgroup.IsComplement (H : Set G) (D : Set G))
    {k : ℕ} (F : (Fin k → G) → V) (hF : Invariant ⊤ F) :
    average (l := l) D F = F := by
  have hcard : (D.card : ℚ_[l]) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hD.nonempty_right
  ext x
  simp only [average, hF ⟨_, Subgroup.mem_top _⟩, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hcard, one_smul]

private theorem average_invariant {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] (H : Subgroup G) (D : Finset G)
    (hD : Subgroup.IsComplement (H : Set G) (D : Set G))
    {k : ℕ} (F : (Fin k → G) → V) (hF : Invariant H F) :
    Invariant ⊤ (average (l := l) D F) := by
  classical
  intro g x
  let p : D → D := fun s ↦ hD.toRightFun ((s : G) * (g : G))
  have hp (s : D) : (s : G) * (g : G) * (p s : G)⁻¹ ∈ H :=
    hD.mul_inv_toRightFun_mem _
  have hrep (s t : D) (ht : (s : G) * (t : G)⁻¹ ∈ H) : s = t := by
    have hs := (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hD (s : G))
    exact hs.unique (by simp) ht
  have hinj : Function.Injective p := by
    intro s t hst
    apply hrep s t
    simpa [hst, mul_assoc] using H.mul_mem (hp s) (H.inv_mem (hp t))
  let π : D ≃ D := Equiv.ofBijective p
    ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
  have he (s : D) : F (fun i ↦ (s : G) * ((g : G) * x i)) =
      F (fun i ↦ (π s : G) * x i) := by
    let h : H := ⟨(s : G) * (g : G) * (π s : G)⁻¹, hp s⟩
    have ht : (fun i ↦ (s : G) * ((g : G) * x i)) =
        (fun i ↦ (h : G) * ((π s : G) * x i)) := by
      funext i
      simp [h, mul_assoc]
    rw [ht, hF]
  simp only [average]
  congr 1
  rw [← Finset.sum_coe_sort D, ← Finset.sum_coe_sort D]
  simp_rw [he]
  exact Equiv.sum_comp π (fun s : D ↦ F (fun i ↦ (s : G) * x i))

private theorem average_continuous {l : ℕ} [Fact l.Prime] {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type v} [AddCommGroup V] [Module ℚ_[l] V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul ℚ_[l] V] (D : Finset G)
    {k : ℕ} (F : (Fin k → G) → V) (hF : Continuous F) :
    Continuous (average (l := l) D F) := by
  apply Continuous.const_smul
  apply continuous_finsetSum D
  intro s hs
  exact hF.comp (continuous_pi (fun i ↦ continuous_const.mul (continuous_apply i)))

private theorem pull_expansion {G : Type u} {V : Type v} [AddCommGroup V]
    {k r t : ℕ} (T : Chain G k →ₗ[ℤ] Chain G r) (a : Fin t → ℤ)
    (α : Fin t → (Fin k → G) → (Fin r → G))
    (hT : ∀ x, T (Finsupp.single x 1) = ∑ j, a j • Finsupp.single (α j x) 1)
    (F : (Fin r → G) → V) (x : Fin k → G) :
    pull T F x = ∑ j, a j • F (α j x) := by
  simp [pull, hT, map_sum, evaluate]

private theorem pull_invariant {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
    {k r : ℕ} (H : Subgroup G) (T : Chain G k →ₗ[ℤ] Chain G r)
    (hT : ∀ h : H, ∀ z, T (translate k (h : G) z) = translate r (h : G) (T z))
    (F : (Fin r → G) → V) (hF : Invariant H F) : Invariant H (pull T F) := by
  intro h x
  have ht : Finsupp.single (fun i ↦ (h : G) * x i) 1 =
      translate k (h : G) (Finsupp.single x 1) := by simp [translate]
  simp only [pull, ht, hT, evaluate_translate H F hF]

private theorem pull_add {G : Type u} {V : Type v} [AddCommGroup V] {k r : ℕ}
    (T : Chain G k →ₗ[ℤ] Chain G r) (F F' : (Fin r → G) → V) :
    pull T (F + F') = pull T F + pull T F' := by
  ext x
  simp [pull, evaluate, Finsupp.linearCombination_apply, Finsupp.sum, smul_add,
    Finset.sum_add_distrib]

private theorem pull_smul {l : ℕ} [Fact l.Prime] {G : Type u} {V : Type v}
    [AddCommGroup V] [Module ℚ_[l] V] {k r : ℕ}
    (T : Chain G k →ₗ[ℤ] Chain G r) (F : (Fin r → G) → V) (c : ℚ_[l]) :
    pull T (c • F) = c • pull T F := by
  ext x
  simp only [pull, evaluate, Finsupp.linearCombination_apply, Finsupp.sum,
    Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact smul_comm _ _ _

private theorem pull_continuous {l : ℕ} [Fact l.Prime] {G : Type u}
    [TopologicalSpace G] {V : Type v} [AddCommGroup V] [Module ℚ_[l] V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℚ_[l] V]
    {k r t : ℕ} (T : Chain G k →ₗ[ℤ] Chain G r) (a : Fin t → ℤ)
    (α : Fin t → C(Fin k → G, Fin r → G))
    (hT : ∀ x, T (Finsupp.single x 1) = ∑ j, a j • Finsupp.single (α j x) 1)
    (F : (Fin r → G) → V) (hF : Continuous F) : Continuous (pull T F) := by
  have he : pull T F = fun x ↦ ∑ j, (a j : ℚ_[l]) • F (α j x) := by
    ext x
    simpa only [Int.cast_smul_eq_zsmul] using
      pull_expansion T a (fun j ↦ α j) hT F x
  rw [he]
  exact continuous_finsetSum _ (fun j _ ↦ (hF.comp (α j).continuous).const_smul _)

private theorem pull_support_zero {G : Type u} {V : Type v} [AddCommGroup V]
    {k r : ℕ} (T : Chain G k →ₗ[ℤ] Chain G r) (E : Set (Fin r → G))
    (hE : ∀ x, ↑(T (Finsupp.single x 1)).support ⊆ E)
    (F : (Fin r → G) → V) (hF : ∀ x ∈ E, F x = 0) : pull T F = 0 := by
  ext x
  apply Finset.sum_eq_zero
  intro y hy
  change (T (Finsupp.single x 1)) y • F y = 0
  rw [hF y (hE x hy), smul_zero]

private theorem pull_homotopy {G : Type u} {V : Type v} [AddCommGroup V]
    (n : ℕ) (A : Chain G (n + 2) →ₗ[ℤ] Chain G (n + 2))
    (Q : Chain G (n + 1) →ₗ[ℤ] Chain G (n + 2))
    (Q' : Chain G (n + 2) →ₗ[ℤ] Chain G (n + 3))
    (hh : ∀ z, z - A z = boundary G (n + 2) (Q' z) + Q (boundary G (n + 1) z))
    (F : (Fin (n + 2) → G) → V) (hF : delta F = 0) :
    F = delta (pull Q F) + pull A F := by
  ext x
  have he := congrArg (evaluate F) (hh (Finsupp.single x 1))
  have hz : evaluate F (boundary G (n + 2) (Q' (Finsupp.single x 1))) = 0 := by
    rw [evaluate_boundary, hF]
    simp [evaluate]
  have hb : evaluate F (Q (boundary G (n + 1) (Finsupp.single x 1))) =
      delta (pull Q F) x := by
    simp only [boundary, Finsupp.linearCombination_single, one_smul,
      map_sum, map_smul, delta, pull]
  rw [map_sub, map_add, evaluate_single, hz, zero_add, hb] at he
  exact (sub_eq_iff_eq_add.mp he)

private theorem average_pull_expansion {l : ℕ} [Fact l.Prime]
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℚ_[l] V]
    {k r t : ℕ} (D : Finset G) (T : Chain G k →ₗ[ℤ] Chain G r) (a : Fin t → ℤ)
    (α : Fin t → (Fin k → G) → (Fin r → G))
    (hT : ∀ x, T (Finsupp.single x 1) = ∑ j, a j • Finsupp.single (α j x) 1)
    (F : (Fin r → G) → V) (x : Fin k → G) :
    average (l := l) D (pull T F) x =
      ∑ s ∈ D, ∑ j, ((a j : ℚ_[l]) / D.card) • F (α j (fun i ↦ s * x i)) := by
  simp only [average, pull_expansion T a α hT, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Int.cast_smul_eq_zsmul ℚ_[l], smul_smul, div_eq_mul_inv, mul_comm]

/-- The homotopy residual and its right-coset average have all the asserted
cochain identities and fixed finite evaluation formulas, uniformly in V.

Source: latest blueprint direct-images (3), agent-written scalar tame-kernel
auxiliary expansion, retained steps 10--12
(blueprint: lem-sfb-coset-averaged-homogeneous-residual).

Proof:
1. Extend each function additively using def-weil-pbc-free-module. Evaluation
   of delta is evaluation after boundary, and evaluation is linear in F.
2. In delta squared pair omissions i<j in the two orders: their coefficients
   are (-1)^(i+j-1) and (-1)^(i+j), so they cancel. Coordinate deletion is
   continuous and commutes with translation.
3. The transversal has positive cardinality. Characteristic zero of Q_l
   (def-weil-l-adic-numbers) makes this cardinality invertible, even if l divides
   it. Each translation is continuous, so the finite average is continuous.
4. For g in G, write s*g=h*t. Right multiplication permutes right cosets,
   so H-invariance and reindexing prove G-invariance of the average.
5. Interchange the two finite sums to commute averaging with delta. A
   G-invariant function has card(D) identical summands and is fixed.
6. The given finite continuous formulas make U F and W F continuous.
   H-equivariance of Q and A and invariance of F give their H-invariance.
7. Evaluate 1-A=boundary Q+Q boundary on a top basis tuple. The first term
   vanishes for a cocycle; the second is delta U F. Thus F=delta U F+W F.
   Apply delta and step 2 to see that W F is a cocycle. Q in top degree is
   available; no A one degree higher is needed.
8. Apply averaging, use steps 4--5, and obtain the averaged decomposition
   and the cocycle equation for the averaged residual.
9. If F vanishes on E, its additive extension kills the stated support of A,
   so W F and its average vanish, independently of the cocycle condition.
   Expand Q and A before averaging: the formulas are sums over (s,j) with
   coefficients k_j/card(D) at the continuous maps b_j(s*x). These maps and
   integers were fixed before V. Distributing finite sums proves linearity.
   No normality, prime-to-l, completeness or cohomology quotient is used. -/
theorem coset_averaged_homogeneous_residual
    (l : ℕ) [Fact l.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.FiniteIndex] (D : Finset G)
    (hD : Subgroup.IsComplement (H : Set G) (D : Set G))
    (n : ℕ) (E : Set (Fin (n + 2) → G))
    (A : ∀ k : ℕ, Chain G k →ₗ[ℤ] Chain G k)
    (Q : ∀ k : ℕ, Chain G k →ₗ[ℤ] Chain G (k + 1))
    (hA0 : A 0 = LinearMap.id) (hQ0 : Q 0 = 0)
    (hAe : ∀ k ≤ n + 2, ∀ h : H, ∀ z : Chain G k,
      A k (translate k (h : G) z) = translate k (h : G) (A k z))
    (hQe : ∀ k ≤ n + 2, ∀ h : H, ∀ z : Chain G k,
      Q k (translate k (h : G) z) = translate (k + 1) (h : G) (Q k z))
    (hchain : ∀ k ≤ n + 1, ∀ z : Chain G (k + 1),
      boundary G k (A (k + 1) z) = A k (boundary G k z))
    (hhomotopy : ∀ k ≤ n + 1, ∀ z : Chain G (k + 1),
      z - A (k + 1) z = boundary G (k + 1) (Q (k + 1) z) + Q k (boundary G k z))
    (tA tQ : ℕ → ℕ)
    (a : ∀ k : ℕ, Fin (tA k) → ℤ) (b : ∀ k : ℕ, Fin (tQ k) → ℤ)
    (α : ∀ k : ℕ, Fin (tA k) → C(Fin k → G, Fin k → G))
    (β : ∀ k : ℕ, Fin (tQ k) → C(Fin k → G, Fin (k + 1) → G))
    (hA : ∀ k, 1 ≤ k → k ≤ n + 2 → ∀ x : Fin k → G,
      A k (Finsupp.single x 1) = ∑ j : Fin (tA k), a k j • Finsupp.single (α k j x) 1)
    (hQ : ∀ k, 1 ≤ k → k ≤ n + 2 → ∀ x : Fin k → G,
      Q k (Finsupp.single x 1) = ∑ j : Fin (tQ k), b k j • Finsupp.single (β k j x) 1)
    (hE : ∀ x : Fin (n + 2) → G,
      ↑(A (n + 2) (Finsupp.single x 1)).support ⊆ E) :
    (∀ (s : G) (j : Fin (tQ (n + 1))),
      Continuous (fun x : Fin (n + 1) → G ↦ β (n + 1) j (fun i ↦ s * x i))) ∧
    (∀ (s : G) (j : Fin (tA (n + 2))),
      Continuous (fun x : Fin (n + 2) → G ↦ α (n + 2) j (fun i ↦ s * x i))) ∧
    ∀ (V : Type v) [AddCommGroup V] [Module ℚ_[l] V] [TopologicalSpace V]
      [ContinuousAdd V] [ContinuousSMul ℚ_[l] V],
      (∀ (k : ℕ) (L : (Fin (k + 1) → G) → V), delta (delta L) = 0) ∧
      (∀ (k : ℕ) (L : (Fin (k + 1) → G) → V),
        Continuous L → Invariant H L →
          Continuous (average (l := l) D L) ∧ Invariant ⊤ (average (l := l) D L)) ∧
      (∀ (k : ℕ) (L : (Fin (k + 1) → G) → V),
        delta (average (l := l) D L) = average (l := l) D (delta L)) ∧
      (∀ (k : ℕ) (L : (Fin (k + 1) → G) → V),
        Invariant ⊤ L → average (l := l) D L = L) ∧
      (∀ F : (Fin (n + 2) → G) → V,
        Continuous F → Invariant ⊤ F →
          Continuous (pull (Q (n + 1)) F) ∧ Invariant H (pull (Q (n + 1)) F) ∧
          Continuous (pull (A (n + 2)) F) ∧ Invariant H (pull (A (n + 2)) F) ∧
          (delta F = 0 →
            F = delta (pull (Q (n + 1)) F) + pull (A (n + 2)) F ∧
            delta (pull (A (n + 2)) F) = 0 ∧
            F = delta (average (l := l) D (pull (Q (n + 1)) F)) +
              average (l := l) D (pull (A (n + 2)) F) ∧
            delta (average (l := l) D (pull (A (n + 2)) F)) = 0) ∧
          ((∀ x ∈ E, F x = 0) →
            pull (A (n + 2)) F = 0 ∧ average (l := l) D (pull (A (n + 2)) F) = 0)) ∧
      (∀ F : (Fin (n + 2) → G) → V, ∀ x : Fin (n + 1) → G,
        average (l := l) D (pull (Q (n + 1)) F) x =
          ∑ s ∈ D, ∑ j : Fin (tQ (n + 1)),
            ((b (n + 1) j : ℚ_[l]) / D.card) • F (β (n + 1) j (fun i ↦ s * x i))) ∧
      (∀ F : (Fin (n + 2) → G) → V, ∀ x : Fin (n + 2) → G,
        average (l := l) D (pull (A (n + 2)) F) x =
          ∑ s ∈ D, ∑ j : Fin (tA (n + 2)),
            ((a (n + 2) j : ℚ_[l]) / D.card) • F (α (n + 2) j (fun i ↦ s * x i))) ∧
      (∀ (F F' : (Fin (n + 2) → G) → V) (c : ℚ_[l]),
        average (l := l) D (pull (Q (n + 1)) (F + F')) =
          average (l := l) D (pull (Q (n + 1)) F) + average (l := l) D (pull (Q (n + 1)) F') ∧
        average (l := l) D (pull (Q (n + 1)) (c • F)) =
          c • average (l := l) D (pull (Q (n + 1)) F)) ∧
      (∀ (F F' : (Fin (n + 2) → G) → V) (c : ℚ_[l]),
        average (l := l) D (pull (A (n + 2)) (F + F')) =
          average (l := l) D (pull (A (n + 2)) F) +
            average (l := l) D (pull (A (n + 2)) F') ∧
        average (l := l) D (pull (A (n + 2)) (c • F)) =
          c • average (l := l) D (pull (A (n + 2)) F)) := by
  classical
  have _ := hA0
  have _ := hQ0
  have _ := hchain
  refine ⟨?_, ?_, ?_⟩
  · intro s j
    exact (β (n + 1) j).continuous.comp
      (continuous_pi (fun i ↦ continuous_const.mul (continuous_apply i)))
  · intro s j
    exact (α (n + 2) j).continuous.comp
      (continuous_pi (fun i ↦ continuous_const.mul (continuous_apply i)))
  · intro V _ _ _ _ _
    refine ⟨delta_squared, ?_, fun _ L ↦ delta_average D L,
      fun _ L hL ↦ average_fixed H D hD L hL, ?_, ?_, ?_, ?_, ?_⟩
    · intro k L hc hi
      exact ⟨average_continuous D L hc, average_invariant H D hD L hi⟩
    · intro F hc hi
      have hFH : Invariant H F := fun h x ↦ hi ⟨h, Subgroup.mem_top _⟩ x
      have hq := hQ (n + 1) (by omega) (by omega)
      have ha := hA (n + 2) (by omega) (by omega)
      refine ⟨pull_continuous (l := l) (Q (n + 1)) (b (n + 1)) (β (n + 1)) hq F hc,
        pull_invariant H (Q (n + 1)) (hQe (n + 1) (by omega)) F hFH,
        pull_continuous (l := l) (A (n + 2)) (a (n + 2)) (α (n + 2)) ha F hc,
        pull_invariant H (A (n + 2)) (hAe (n + 2) (by omega)) F hFH, ?_, ?_⟩
      · intro hd
        have he := pull_homotopy n (A (n + 2)) (Q (n + 1)) (Q (n + 2))
          (hhomotopy (n + 1) le_rfl) F hd
        have hw : delta (pull (A (n + 2)) F) = 0 := by
          have hh := congrArg delta he
          rw [delta_add, delta_squared, zero_add, hd] at hh
          exact hh.symm
        refine ⟨he, hw, ?_, ?_⟩
        · calc
            F = average (l := l) D F := (average_fixed H D hD F hi).symm
            _ = average (l := l) D
                (delta (pull (Q (n + 1)) F) + pull (A (n + 2)) F) :=
              congrArg (average (l := l) D) he
            _ = _ := by rw [average_add, ← delta_average]
        · rw [delta_average, hw, average_zero]
      · intro hzero
        have hz := pull_support_zero (A (n + 2)) E hE F hzero
        exact ⟨hz, by rw [hz, average_zero]⟩
    · intro F x
      exact average_pull_expansion D (Q (n + 1)) (b (n + 1))
        (fun j ↦ β (n + 1) j) (hQ (n + 1) (by omega) (by omega)) F x
    · intro F x
      exact average_pull_expansion D (A (n + 2)) (a (n + 2))
        (fun j ↦ α (n + 2) j) (hA (n + 2) (by omega) (by omega)) F x
    · intro F F' c
      constructor
      · rw [pull_add, average_add]
      · rw [pull_smul, average_smul]
    · intro F F' c
      constructor
      · rw [pull_add, average_add]
      · rw [pull_smul, average_smul]

end ContinuousCohomology.CosetResidual
