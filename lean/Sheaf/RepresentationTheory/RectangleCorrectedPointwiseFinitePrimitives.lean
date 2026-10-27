/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer

/-! # Rectangle-corrected pointwise finite primitives

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated analytic auxiliary lemma, old steps 8--9; exact norm-topological
reference WANTED (blueprint: lem-sfb-rectangle-corrected-pointwise-finite-primitives).

The degree is `n + 1`. The named component cochains are pinned by their evaluations,
so their binders introduce no additional choice or assumption. All finite evaluation
formulas are fixed before the coefficient field is specialized.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped BigOperators
open Filter

namespace ContinuousCohomology

/-- Abbreviation for the existing continuous differential with trivial action.
In degree zero its two terms cancel, so it is zero.

Source: the displayed differential of the agent analytic lemma motivated by blueprint
main-20261015, direct-images proof (3)
(blueprint: lem-sfb-rectangle-corrected-pointwise-finite-primitives). -/
abbrev rectangleTrivialD (E : Type u) [NormedField E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (r : ℕ) :=
  continuousInhomogeneousD (TopRep.of (ContRepresentation.trivial E G E))
    continuous_snd r

private theorem map_sign_smul
    {E : Type*} [Field E] {K : Type*} [Field K]
    (f : E →+ K) (m : ℕ) (x : E) :
    f ((-1 : E) ^ m • x) = (-1 : K) ^ m • f x := by
  rcases Nat.even_or_odd m with hm | hm <;> simp [hm.neg_one_pow]

private theorem rectangleTrivialD_natural
    {E : Type*} [NormedField E] {K : Type*} [NormedField K]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : E →+ K) (m : ℕ) (c : C(Fin m → G, E)) (c' : C(Fin m → G, K))
    (hc : ∀ x, c' x = f (c x)) (x : Fin (m + 1) → G) :
    rectangleTrivialD K G m c' x = f (rectangleTrivialD E G m c x) := by
  change c' (fun i ↦ x i.succ) +
      ∑ j : Fin (m + 1), (-1 : K) ^ (j.val + 1) •
        c' (Fin.contractNth j (· * ·) x) =
    f (c (fun i ↦ x i.succ) +
      ∑ j : Fin (m + 1), (-1 : E) ^ (j.val + 1) •
        c (Fin.contractNth j (· * ·) x))
  simp only [hc, map_add, map_sum, map_sign_smul]

/-- Rectangle correction produces continuous finite-field primitives, uniformly small
and pointwise eventually zero. The residual is eventually the zero entire cochain.
The `T` and `R` operators in the ambient and intermediate fields have exactly the
same finite evaluation formulas. All norms are the actual supremum norms.

Source: main-20261015 blueprint, direct-images proof (3), agent-formulated analytic
lemma, old steps 8--9; exact norm-topological reference WANTED
(blueprint: lem-sfb-rectangle-corrected-pointwise-finite-primitives).

Proof:
1. Since F_(i-1) is contained in F_i, the projection difference is F_i-valued,
   including e_0 = p_0 z. Linearity commutes with the finite differential, so e_i
   is a cocycle. The evaluation equation uniquely specifies these cochains.
2. For each fixed rectangle index the operators preserve continuous parameter
   families. Local constancy of k_i pastes the fixed-index formulas into continuous
   r_i and b_i; the finite image of k_i follows from compactness of S.
3. The residual is a cocycle. Apply d h_i = id to it and add the identity
   d T_j + R_j = id, giving d b_i = e_i in each parameter fibre.
4. The operator bounds and the ultrametric inequality bound each value of b_i by
   the supremum norm of e_i. Taking suprema gives the stated norm bound and limit.
5. Fix s and its stabilized rectangle j. Beyond N_j + 1 both projections fix every
   homogeneous value of z on that rectangle. Their difference vanishes there;
   the residual-vanishing hypothesis makes R_j e_i(s) the zero entire cochain.
   Coefficient independence identifies the ambient and finite-field calculations.
   Linearity gives h_i(0) = 0, hence b_i(s,x) = T_j e_i(s)(x).
6. Fix x. The last expression is a fixed finite sum of evaluations of e_i. Take
   the maximum of their finitely many eventual-zero thresholds and the thresholds
   from step 5. Every summand then vanishes. Empty evaluation lists give zero.
   For n = 0, corresponding to degree one, the primitive domain is the singleton
   G^0 and d^0 = 0. For empty S all cochains and their norms are zero.
All six steps are elementary from the explicitly assumed identities and bounds;
the DAG proof has no proof dependencies.
-/
theorem exists_rectangleCorrectedPointwiseFinitePrimitives
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [NontriviallyNormedField Ω] [NormedAlgebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (hΩ : ∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (S : Profinite.{w})
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (n : ℕ)
    (F : ℕ → IntermediateField ℚ_[l] Ω) (hF : Monotone F)
    [∀ i : ℕ, FiniteDimensional ℚ_[l] (F i)]
    (p : ℕ → Ω →L[ℚ_[l]] Ω)
    (hp_range : ∀ (i : ℕ) (x : Ω), p i x ∈ F i)
    (hp_fix : ∀ (i : ℕ) (x : F i), p i x = x)
    (hp_norm : ∀ (i : ℕ) (x : Ω), ‖p i x‖ ≤ ‖x‖)
    (z : C(S × (Fin (n + 1) → G), Ω))
    (hz : ∀ s : S, rectangleTrivialD Ω G (n + 1) (z.curry s) = 0)
    (e : ∀ i : ℕ, C(S × (Fin (n + 1) → G), F i))
    (he : ∀ (i : ℕ) (s : S) (x : Fin (n + 1) → G),
      (e i (s, x) : Ω) = p i (z (s, x)) -
        if i = 0 then 0 else p (i - 1) (z (s, x)))
    (he_norm : Tendsto (fun i : ℕ ↦ ‖e i‖) atTop (nhds 0))
    (he_zero : ∀ (s : S) (x : Fin (n + 1) → G),
      ∀ᶠ i : ℕ in atTop, e i (s, x) = 0)
    (H : ℕ+ → OpenSubgroup G) (hH : ∀ j : ℕ+, (H j).toSubgroup.Normal)
    (a : ℕ+ → Fin (n + 2) → G) (N : ℕ+ → ℕ)
    (k : ℕ → LocallyConstant S ℕ+) (j : S → ℕ+)
    (hk : ∀ s : S, ∀ᶠ i : ℕ in atTop, k i s = j s)
    (hrectangle : ∀ (s : S) (x : Fin (n + 2) → H (j s)),
      z (s, fun q ↦ ((x q.castSucc : G) * a (j s) q.castSucc)⁻¹ *
        ((x q.succ : G) * a (j s) q.succ)) ∈ F (N (j s)))
    (t r : ℕ+ → ℕ)
    (α : ∀ j : ℕ+, Fin (t j) → ℚ_[l])
    (β : ∀ j : ℕ+, Fin (r j) → ℚ_[l])
    (ψ : ∀ j : ℕ+, Fin (t j) → C(Fin n → G, Fin (n + 1) → G))
    (χ : ∀ j : ℕ+, Fin (r j) → C(Fin (n + 1) → G, Fin (n + 1) → G))
    (hα : ∀ (j : ℕ+) (q : Fin (t j)), ‖α j q‖ ≤ 1)
    (hβ : ∀ (j : ℕ+) (q : Fin (r j)), ‖β j q‖ ≤ 1)
    (TΩ : ℕ+ → C(Fin (n + 1) → G, Ω) →ₗ[ℚ_[l]] C(Fin n → G, Ω))
    (RΩ : ℕ+ → C(Fin (n + 1) → G, Ω) →ₗ[ℚ_[l]] C(Fin (n + 1) → G, Ω))
    (T : ∀ i : ℕ, ℕ+ → C(Fin (n + 1) → G, F i) →ₗ[ℚ_[l]] C(Fin n → G, F i))
    (R : ∀ i : ℕ, ℕ+ →
      C(Fin (n + 1) → G, F i) →ₗ[ℚ_[l]] C(Fin (n + 1) → G, F i))
    (hTΩ : ∀ (j : ℕ+) (c : C(Fin (n + 1) → G, Ω)) (x : Fin n → G),
      TΩ j c x = ∑ q : Fin (t j), α j q • c (ψ j q x))
    (hRΩ : ∀ (j : ℕ+) (c : C(Fin (n + 1) → G, Ω)) (x : Fin (n + 1) → G),
      RΩ j c x = ∑ q : Fin (r j), β j q • c (χ j q x))
    (hT : ∀ (i : ℕ) (j : ℕ+) (c : C(Fin (n + 1) → G, F i)) (x : Fin n → G),
      T i j c x = ∑ q : Fin (t j), α j q • c (ψ j q x))
    (hR : ∀ (i : ℕ) (j : ℕ+) (c : C(Fin (n + 1) → G, F i))
      (x : Fin (n + 1) → G), R i j c x = ∑ q : Fin (r j), β j q • c (χ j q x))
    (hopΩ : ∀ (j : ℕ+) (c : C(Fin (n + 1) → G, Ω)),
      ‖TΩ j c‖ ≤ ‖c‖ ∧ ‖RΩ j c‖ ≤ ‖c‖ ∧
      (rectangleTrivialD Ω G (n + 1) c = 0 →
        rectangleTrivialD Ω G n (TΩ j c) + RΩ j c = c ∧
        rectangleTrivialD Ω G (n + 1) (RΩ j c) = 0 ∧
        ((∀ x : Fin (n + 2) → H j,
          c (fun q ↦ ((x q.castSucc : G) * a j q.castSucc)⁻¹ *
            ((x q.succ : G) * a j q.succ)) = 0) → RΩ j c = 0)))
    (hop : ∀ (i : ℕ) (j : ℕ+) (c : C(Fin (n + 1) → G, F i)),
      ‖T i j c‖ ≤ ‖c‖ ∧ ‖R i j c‖ ≤ ‖c‖ ∧
      (rectangleTrivialD (F i) G (n + 1) c = 0 →
        rectangleTrivialD (F i) G n (T i j c) + R i j c = c ∧
        rectangleTrivialD (F i) G (n + 1) (R i j c) = 0 ∧
        ((∀ x : Fin (n + 2) → H j,
          c (fun q ↦ ((x q.castSucc : G) * a j q.castSucc)⁻¹ *
            ((x q.succ : G) * a j q.succ)) = 0) → R i j c = 0)))
    (h : ∀ i : ℕ, C(Fin (n + 1) → G, F i) →ₗ[F i] C(Fin n → G, F i))
    (hh_norm : ∀ (i : ℕ) (c : C(Fin (n + 1) → G, F i)), ‖h i c‖ ≤ ‖c‖)
    (hh_d : ∀ (i : ℕ) (c : C(Fin (n + 1) → G, F i)),
      rectangleTrivialD (F i) G (n + 1) c = 0 → rectangleTrivialD (F i) G n (h i c) = c)
    (hh_family : ∀ (i : ℕ) (P : Profinite.{w})
      (c : C(P × (Fin (n + 1) → G), F i)),
      Continuous (fun q : P × (Fin n → G) ↦ h i (c.curry q.1) q.2)) :
    ∃ (res : ∀ i : ℕ, C(S × (Fin (n + 1) → G), F i))
      (b : ∀ i : ℕ, C(S × (Fin n → G), F i)),
      (∀ (i : ℕ) (s : S) (x : Fin (n + 1) → G),
        res i (s, x) = R i (k i s) ((e i).curry s) x) ∧
      (∀ (i : ℕ) (s : S) (x : Fin n → G),
        b i (s, x) = T i (k i s) ((e i).curry s) x +
          h i ((res i).curry s) x) ∧
      (∀ (i : ℕ) (s : S), rectangleTrivialD (F i) G n ((b i).curry s) = (e i).curry s) ∧
      (∀ i : ℕ, ‖b i‖ ≤ ‖e i‖) ∧
      Tendsto (fun i : ℕ ↦ ‖b i‖) atTop (nhds 0) ∧
      (∀ (s : S) (x : Fin n → G), ∀ᶠ i : ℕ in atTop, b i (s, x) = 0) ∧
      ∀ s : S, ∀ᶠ i : ℕ in atTop,
        R i (j s) ((e i).curry s) = 0 ∧
        (∀ x : Fin (n + 1) → G, res i (s, x) = 0) ∧
        (∀ x : Fin n → G, b i (s, x) = T i (j s) ((e i).curry s) x ∧
          b i (s, x) = ∑ q : Fin (t (j s)), α (j s) q • e i (s, ψ (j s) q x)) := by
  classical
  -- The finite-field identities and bounds already include these ambient consequences.
  have _ := hp_range
  have _ := hp_norm
  have _ := hH
  have _ := hα
  have _ := hβ
  have _ := hTΩ
  have _ := hRΩ
  have _ := hopΩ
  have he_cocycle (i : ℕ) (s : S) :
      rectangleTrivialD (F i) G (n + 1) ((e i).curry s) = 0 := by
    let c : C(Fin (n + 1) → G, Ω) :=
      ⟨fun x ↦ (e i (s, x) : Ω), continuous_subtype_val.comp ((e i).curry s).continuous⟩
    let f : Ω →+ Ω := (p i).toLinearMap.toAddMonoidHom -
      if i = 0 then 0 else (p (i - 1)).toLinearMap.toAddMonoidHom
    have hc : rectangleTrivialD Ω G (n + 1) c = 0 := by
      ext x
      rw [rectangleTrivialD_natural f (n + 1) (z.curry s) c]
      · rw [hz s, ContinuousMap.zero_apply, map_zero]
      · intro y
        by_cases hi : i = 0 <;> simpa [c, f, hi] using he i s y
    apply ContinuousMap.ext
    intro x
    apply Subtype.val_injective
    change ((rectangleTrivialD (F i) G (n + 1) ((e i).curry s) x : F i) : Ω) = 0
    exact (rectangleTrivialD_natural (F i).subtype.toAddMonoidHom
      (n + 1) ((e i).curry s) c (fun _ ↦ rfl) x).symm.trans
        (congrArg (fun c ↦ c x) hc)
  have hRcont (i : ℕ) (j' : ℕ+) : Continuous
      (fun q : S × (Fin (n + 1) → G) ↦ R i j' ((e i).curry q.1) q.2) := by
    simp_rw [hR]
    apply continuous_finsetSum
    intro q _
    change Continuous (fun a : S × (Fin (n + 1) → G) ↦
      β j' q • e i (a.1, χ j' q a.2))
    exact ((e i).continuous.comp
      (continuous_fst.prodMk ((χ j' q).continuous.comp continuous_snd))).const_smul
        (β j' q)
  have hTcont (i : ℕ) (j' : ℕ+) : Continuous
      (fun q : S × (Fin n → G) ↦ T i j' ((e i).curry q.1) q.2) := by
    simp_rw [hT]
    apply continuous_finsetSum
    intro q _
    change Continuous (fun a : S × (Fin n → G) ↦
      α j' q • e i (a.1, ψ j' q a.2))
    exact ((e i).continuous.comp
      (continuous_fst.prodMk ((ψ j' q).continuous.comp continuous_snd))).const_smul
        (α j' q)
  have hselect {X : Type v} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]
      (i : ℕ) (f : ℕ+ → S × X → Y) (hf : ∀ j', Continuous (f j')) :
      Continuous (fun q : S × X ↦ f (k i q.1) q) := by
    rw [continuous_iff_continuousAt]
    intro q
    apply (hf (k i q.1)).continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually
      ((k i).isLocallyConstant.eventually_eq q.1)] with y hy
    change k i y.1 = k i q.1 at hy
    rw [hy]
  let res : ∀ i : ℕ, C(S × (Fin (n + 1) → G), F i) := fun i ↦
    ⟨fun q ↦ R i (k i q.1) ((e i).curry q.1) q.2,
      by exact hselect i (fun j' q ↦ R i j' ((e i).curry q.1) q.2) (hRcont i)⟩
  let b : ∀ i : ℕ, C(S × (Fin n → G), F i) := fun i ↦
    ⟨fun q ↦ T i (k i q.1) ((e i).curry q.1) q.2 + h i ((res i).curry q.1) q.2,
      by exact (hselect i (fun j' q ↦ T i j' ((e i).curry q.1) q.2)
        (hTcont i)).add (hh_family i S (res i))⟩
  have hres (i : ℕ) (s : S) :
      (res i).curry s = R i (k i s) ((e i).curry s) := by rfl
  have hb (i : ℕ) (s : S) :
      (b i).curry s = T i (k i s) ((e i).curry s) + h i ((res i).curry s) := by rfl
  have hprimitive (i : ℕ) (s : S) :
      rectangleTrivialD (F i) G n ((b i).curry s) = (e i).curry s := by
    rw [hb, map_add, hh_d]
    · rw [hres]
      exact (hop i (k i s) ((e i).curry s)).2.2 (he_cocycle i s) |>.1
    · rw [hres]
      exact (hop i (k i s) ((e i).curry s)).2.2 (he_cocycle i s) |>.2.1
  have henorm (i : ℕ) (s : S) : ‖(e i).curry s‖ ≤ ‖e i‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    exact (e i).norm_coe_le_norm (s, x)
  have hbnorm (i : ℕ) : ‖b i‖ ≤ ‖e i‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    rintro ⟨s, x⟩
    change ‖(T i (k i s) ((e i).curry s) x : F i) +
      h i ((res i).curry s) x‖ ≤ ‖e i‖
    have hu (u v : F i) : ‖u + v‖ ≤ max ‖u‖ ‖v‖ := hΩ u v
    apply (hu _ _).trans (max_le _ _)
    · exact ((T i (k i s) ((e i).curry s)).norm_coe_le_norm x).trans
        ((hop i (k i s) ((e i).curry s)).1.trans (henorm i s))
    · apply ((h i ((res i).curry s)).norm_coe_le_norm x).trans
      apply (hh_norm i _).trans
      rw [hres]
      exact (hop i (k i s) ((e i).curry s)).2.1.trans (henorm i s)
  have hstabilize (s : S) : ∀ᶠ i : ℕ in atTop,
      R i (j s) ((e i).curry s) = 0 ∧
      (∀ x : Fin (n + 1) → G, res i (s, x) = 0) ∧
      (∀ x : Fin n → G, b i (s, x) = T i (j s) ((e i).curry s) x ∧
        b i (s, x) = ∑ q : Fin (t (j s)), α (j s) q • e i (s, ψ (j s) q x)) := by
    filter_upwards [hk s, eventually_ge_atTop (N (j s) + 1)] with i hki hi
    have hzrect : ∀ x : Fin (n + 2) → H (j s),
        (e i).curry s (fun q ↦ ((x q.castSucc : G) * a (j s) q.castSucc)⁻¹ *
          ((x q.succ : G) * a (j s) q.succ)) = 0 := by
      intro x
      apply Subtype.val_injective
      change (e i (s, _) : Ω) = 0
      rw [he, if_neg (by omega)]
      have hi' : N (j s) ≤ i - 1 := by omega
      have hvi := hF (show N (j s) ≤ i by omega) (hrectangle s x)
      have hvi' := hF hi' (hrectangle s x)
      rw [hp_fix i ⟨_, hvi⟩, hp_fix (i - 1) ⟨_, hvi'⟩, sub_self]
    have hrzero := (hop i (j s) ((e i).curry s)).2.2 (he_cocycle i s) |>.2.2 hzrect
    have hr : (res i).curry s = 0 := by rw [hres, hki, hrzero]
    refine ⟨hrzero, ?_, ?_⟩
    · intro x
      exact congrArg (fun c ↦ c x) hr
    · intro x
      have hb' : b i (s, x) = T i (j s) ((e i).curry s) x := by
        change T i (k i s) ((e i).curry s) x + h i ((res i).curry s) x = _
        rw [hki, hr, map_zero, ContinuousMap.zero_apply, add_zero]
      exact ⟨hb', hb'.trans (hT i (j s) ((e i).curry s) x)⟩
  refine ⟨res, b, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), hprimitive, hbnorm, ?_, ?_,
    hstabilize⟩
  · exact squeeze_zero (fun i ↦ norm_nonneg (b i)) hbnorm he_norm
  · intro s x
    filter_upwards [hstabilize s,
      eventually_all.2 (fun q : Fin (t (j s)) ↦ he_zero s (ψ (j s) q x))] with i hi hzero
    rw [(hi.2.2 x).2]
    exact Finset.sum_eq_zero (fun q _ ↦ by rw [hzero q, smul_zero])

end ContinuousCohomology
