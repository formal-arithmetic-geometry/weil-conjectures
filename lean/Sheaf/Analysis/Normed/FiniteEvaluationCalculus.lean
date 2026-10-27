/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Nonarchimedean finite-evaluation calculus

Source: current Weil blueprint, six-functors basics, CTF direct-images proof, paragraph (3),
agent-formulated scalar tame-kernel expansion, retained rectangle-replacement steps 12–14
(blueprint: lem-sfb-nonarchimedean-finite-evaluation-calculus).

The auxiliary maps below are actual finite sums of Mathlib's precomposition linear maps.
They require neither compactness nor completeness. Compactness is used only for the real
supremum norms in the theorem. Parameters retain their given topology and may be empty.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t s z j a r

open scoped BigOperators

namespace ContinuousMap

/-- The fixed finite evaluation formula as a linear map on continuous functions.
Source: CTF direct-images proof, paragraph (3), scalar tame-kernel expansion, step 12
(blueprint: lem-sfb-nonarchimedean-finite-evaluation-calculus).
This is a finite sum of the existing precomposition maps, with the stated coefficients. -/
noncomputable def finiteEvaluationLinearMap
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l]) :
    C(X, V) →ₗ[ℚ_[l]] C(Y, V) :=
  ∑ i : I, c i • (ContinuousMap.compCLM ℚ_[l] V (b i)).toLinearMap

/-- The same finite formula on a parameter family, leaving the parameter fixed.
Source: CTF direct-images proof, paragraph (3), scalar tame-kernel expansion, step 14
(blueprint: lem-sfb-nonarchimedean-finite-evaluation-calculus).
The product maps and the finite evaluation map are existing, actual constructions. -/
noncomputable def finiteEvaluationParameterMap
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (S : Type s) [TopologicalSpace S] :
    C(S × X, V) →ₗ[ℚ_[l]] C(S × Y, V) :=
  finiteEvaluationLinearMap l V (fun i ↦ (ContinuousMap.id S).prodMap (b i)) c

private theorem finiteEvaluation_apply
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (f : C(X, V)) (y : Y) :
    finiteEvaluationLinearMap l V b c f y = ∑ i : I, c i • f (b i y) := by
  simp [finiteEvaluationLinearMap, LinearMap.sum_apply, ContinuousMap.sum_apply]

private theorem finiteEvaluation_bound
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    (hV : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖)
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i, ‖c i‖ ≤ B) (f : C(X, V)) :
    ‖finiteEvaluationLinearMap l V b c f‖ ≤ B * ‖f‖ := by
  have : IsUltrametricDist V :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm hV
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro y
  rw [finiteEvaluation_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hB (norm_nonneg f))
  intro i _
  rw [norm_smul]
  exact mul_le_mul (hc i) (f.norm_coe_le_norm (b i y)) (norm_nonneg _) hB

private theorem finiteEvaluation_parameter_apply
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (S : Type s) [TopologicalSpace S] (f : C(S × X, V)) (p : S × Y) :
    finiteEvaluationParameterMap l V b c S f p =
      ∑ i : I, c i • f (p.1, b i p.2) := by
  exact finiteEvaluation_apply l V _ c f p

private theorem finiteEvaluation_slice
    (l : ℕ) [Fact l.Prime]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    {I : Type t} [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (S : Type s) [TopologicalSpace S] (f : C(S × X, V)) (q : S) (y : Y) :
    finiteEvaluationParameterMap l V b c S f (q, y) =
      finiteEvaluationLinearMap l V b c
        (f.comp ((ContinuousMap.const X q).prodMk (ContinuousMap.id X))) y := by
  simp [finiteEvaluation_parameter_apply, finiteEvaluation_apply]

/-- Finite scalar evaluation formulas have the stated ultrametric bounds, preserve all
linear subspaces, commute with restriction to parameter slices and with composition, and
are contractive for integer coefficients divided by a positive integer prime to `l`.
Source: current Weil blueprint, CTF direct-images proof, paragraph (3), agent-formulated
scalar tame-kernel expansion, retained rectangle-replacement steps 12–14
(blueprint: lem-sfb-nonarchimedean-finite-evaluation-calculus).

Proof:
1. Each fixed evaluation is continuous; fixed scalar multiplication and finite addition
   are continuous in the norm topology. Distributivity gives the linear map, implemented
   above by the sum of Mathlib precomposition linear maps.
2. Mathlib ContinuousMap.norm_coe_le_norm bounds the pointwise norms, and
   ContinuousMap.norm_eq_iSup_norm identifies their real supremum with the function norm.
   Apply both to f on X and to its finite-evaluation image on Y.
3. Each summand has norm at most B times the input supremum norm, by norm_smul. Induct
   through the finite sum using the ultrametric inequality, starting with zero and B ≥ 0.
   Taking suprema gives the bound. A submodule contains zero and is stable under sums
   and scalar multiplication; no topological closedness is used.
4. Precompose each term with (s,y) ↦ (s,b_i(y)). This map is continuous for any S.
   Finite sums remain continuous, and substitution gives the slice equation. For a
   finite linear identity between evaluation formulas, apply its slice identity at s
   and then at y. Extensionality also gives uniqueness when S is empty.
5. Expand a composite into the double sum and distribute scalar multiplication.
   Index the resulting fixed formula by J × I, with maps b_j ∘ c_k and coefficients
   μ_k λ_j. Precomposition simply replaces b_j by b_j ∘ u. These choices precede V
   and do not use it. Empty index types give zero sums throughout.
6. By def-weil-l-adic-numbers, integers have l-adic norm at most one. A positive
   integer m prime to l has norm one, so norm_div bounds every k/m by one. Apply
   the bound with B = 1, including to the precomposed maps. Subspace and parameter
   conclusions apply to these same coefficients. The zero vector space and singleton
   compact domains require no exception; no limits in V and no completeness are used.
-/
theorem nonarchimedean_finiteEvaluation_calculus
    (l : ℕ) [Fact l.Prime]
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (I : Type t) [Fintype I] (b : I → C(Y, X)) (c : I → ℚ_[l])
    (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i, ‖c i‖ ≤ B)
    (V : Type w) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    (hV : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖) :
    (∀ (f : C(X, V)) (y : Y),
      finiteEvaluationLinearMap l V b c f y = ∑ i : I, c i • f (b i y)) ∧
    (∀ f : C(X, V),
      BddAbove (Set.range (fun x : X ↦ ‖f x‖)) ∧
      BddAbove (Set.range (fun y : Y ↦ ‖finiteEvaluationLinearMap l V b c f y‖)) ∧
      ‖f‖ = ⨆ x : X, ‖f x‖ ∧
      ‖finiteEvaluationLinearMap l V b c f‖ =
        ⨆ y : Y, ‖finiteEvaluationLinearMap l V b c f y‖ ∧
      ‖finiteEvaluationLinearMap l V b c f‖ ≤ B * ‖f‖) ∧
    (∀ (W : Submodule ℚ_[l] V) (f : C(X, V)),
      (∀ x, f x ∈ W) → ∀ y, finiteEvaluationLinearMap l V b c f y ∈ W) ∧
    (∀ (S : Type s) [TopologicalSpace S],
      (∀ f : C(S × X, V),
        Continuous (fun p : S × Y ↦ ∑ i : I, c i • f (p.1, b i p.2)) ∧
        (∀ p : S × Y,
          finiteEvaluationParameterMap l V b c S f p =
            ∑ i : I, c i • f (p.1, b i p.2)) ∧
        (∀ (q : S) (y : Y),
          finiteEvaluationParameterMap l V b c S f (q, y) =
            finiteEvaluationLinearMap l V b c
              (f.comp ((ContinuousMap.const X q).prodMk (ContinuousMap.id X))) y)) ∧
      (∀ (A : Type a) [Fintype A] (J : A → Type r) [∀ q, Fintype (J q)]
        (d : ∀ q, J q → C(Y, X)) (e : ∀ q, J q → ℚ_[l])
        (α : A → ℚ_[l]) (f : A → C(S × X, V)),
        (∀ (q : S) (y : Y),
          ∑ k : A, α k • finiteEvaluationLinearMap l V (d k) (e k)
            ((f k).comp ((ContinuousMap.const X q).prodMk (ContinuousMap.id X))) y = 0) →
        ∀ p : S × Y,
          ∑ k : A, α k • finiteEvaluationParameterMap l V (d k) (e k) S (f k) p = 0) ∧
      (IsEmpty S → ∀ f g : C(S × Y, V), f = g)) ∧
    (IsEmpty I → finiteEvaluationLinearMap l V b c = 0 ∧
      ∀ (S : Type s) [TopologicalSpace S], finiteEvaluationParameterMap l V b c S = 0) ∧
    (∀ (Z : Type z) [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
      (J : Type j) [Fintype J] (d : J → C(Z, Y)) (e : J → ℚ_[l]),
      (finiteEvaluationLinearMap l V d e).comp (finiteEvaluationLinearMap l V b c) =
        finiteEvaluationLinearMap l V
          (fun q : J × I ↦ (b q.2).comp (d q.1)) (fun q ↦ e q.1 * c q.2)) ∧
    (∀ (Z : Type z) [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
      (u : C(Z, Y)) (f : C(X, V)),
      (finiteEvaluationLinearMap l V b c f).comp u =
        finiteEvaluationLinearMap l V (fun i ↦ (b i).comp u) c f) ∧
    (∀ (m : ℕ), 0 < m → Nat.Coprime m l →
      (∀ k : ℤ, ‖(k : ℚ_[l]) / (m : ℚ_[l])‖ ≤ 1) ∧
      (∀ (k : I → ℤ) (f : C(X, V)),
        ‖finiteEvaluationLinearMap l V b (fun i ↦ (k i : ℚ_[l]) / (m : ℚ_[l])) f‖ ≤
          ‖f‖) ∧
      (∀ (Z : Type z) [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
        (u : C(Z, Y)) (k : I → ℤ) (f : C(X, V)),
        ‖finiteEvaluationLinearMap l V (fun i ↦ (b i).comp u)
          (fun i ↦ (k i : ℚ_[l]) / (m : ℚ_[l])) f‖ ≤ ‖f‖)) := by
  classical
  refine ⟨finiteEvaluation_apply l V b c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨?_, ?_, f.norm_eq_iSup_norm, (finiteEvaluationLinearMap l V b c f).norm_eq_iSup_norm,
      finiteEvaluation_bound l V hV b c B hB hc f⟩
    · exact ⟨‖f‖, by rintro _ ⟨x, rfl⟩; exact f.norm_coe_le_norm x⟩
    · exact ⟨‖finiteEvaluationLinearMap l V b c f‖,
        by rintro _ ⟨y, rfl⟩; exact (finiteEvaluationLinearMap l V b c f).norm_coe_le_norm y⟩
  · intro W f hf y
    rw [finiteEvaluation_apply]
    exact W.sum_mem fun i _ ↦ W.smul_mem (c i) (hf (b i y))
  · intro S _
    refine ⟨?_, ?_, ?_⟩
    · intro f
      refine ⟨?_, finiteEvaluation_parameter_apply l V b c S f,
        finiteEvaluation_slice l V b c S f⟩
      exact (finiteEvaluationParameterMap l V b c S f).continuous.congr
        (finiteEvaluation_parameter_apply l V b c S f)
    · intro A _ J _ d e α f h p
      rcases p with ⟨q, y⟩
      simpa only [finiteEvaluation_slice] using h q y
    · intro h f g
      exact ContinuousMap.ext fun p ↦ isEmptyElim p.1
  · intro h
    constructor
    · simp [finiteEvaluationLinearMap]
    · intro S _
      simp [finiteEvaluationParameterMap, finiteEvaluationLinearMap]
  · intro Z _ _ _ J _ d e
    ext f z
    simp [finiteEvaluation_apply, LinearMap.comp_apply, Finset.smul_sum,
      smul_smul, Fintype.sum_prod_type]
  · intro Z _ _ _ u f
    ext z
    simp [finiteEvaluation_apply]
  · intro m _ hm
    have hcoeff : ∀ k : ℤ, ‖(k : ℚ_[l]) / (m : ℚ_[l])‖ ≤ 1 := by
      intro k
      rw [norm_div, (Padic.norm_natCast_eq_one_iff (p := l)).mpr hm.symm, div_one]
      exact Padic.norm_int_le_one k
    refine ⟨hcoeff, ?_, ?_⟩
    · intro k f
      simpa only [one_mul] using
        finiteEvaluation_bound l V hV b (fun i ↦ (k i : ℚ_[l]) / (m : ℚ_[l]))
          1 zero_le_one (fun i ↦ hcoeff (k i)) f
    · intro Z _ _ _ u k f
      simpa only [one_mul] using
        finiteEvaluation_bound l V hV (fun i ↦ (b i).comp u)
          (fun i ↦ (k i : ℚ_[l]) / (m : ℚ_[l])) 1 zero_le_one
          (fun i ↦ hcoeff (k i)) f

end ContinuousMap
