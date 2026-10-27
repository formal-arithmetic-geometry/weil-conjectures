/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Continuous algebraic coordinate projections and split reindexings

Source: blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary
(blueprint: lem-sfb-bounded-coordinate-split-projections).

The auxiliary is extracted from the returned reconstruction proof; the blueprint paragraph
supplies its context, rather than an external proof of this coordinate lemma. The basis is
algebraic, so every expansion and every sum below is finite. No completeness is assumed.

## Main statements

* `Module.Basis.bounded_coordinate_split_projections`: continuous coordinates, matrix units,
  rank-one maps, arbitrary coordinate projections, and the finite overlap identities.
* `Module.Basis.bounded_coordinate_split_reindexing`: the natural-number case, including an
  increasing enumeration of each infinite subset and the two bounded split operators.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module.Basis


private theorem coeff_le_max {K : Type u} [NormedField K] {J : Type w}
    (t : J →₀ K) (j : J) :
    ‖t j‖₊ ≤ t.support.sup (fun k ↦ ‖t k‖₊) := by
  classical
  by_cases h : j ∈ t.support
  · exact Finset.le_sup (f := fun k ↦ ‖t k‖₊) h
  · simp [Finsupp.notMem_support_iff.mp h]

private theorem max_le_norm {K : Type u} [NormedField K]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V]
    {J : Type w} (b : Module.Basis J K V) (c : ℝ) (hc : 0 < c)
    (hb : ∀ t : J →₀ K,
      c * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ) ≤ ‖b.repr.symm t‖)
    (v : V) :
    (↑((b.repr v).support.sup (fun j ↦ ‖b.repr v j‖₊)) : ℝ) ≤ c⁻¹ * ‖v‖ := by
  have h := hb (b.repr v)
  simp only [LinearEquiv.symm_apply_apply] at h
  exact (le_inv_mul_iff₀ hc).2 h

private theorem bound_of_coeff_bound {K : Type u} [NormedField K]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V]
    {J : Type w} (b : Module.Basis J K V) (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hb : ∀ t : J →₀ K,
      c * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ) ≤ ‖b.repr.symm t‖ ∧
      ‖b.repr.symm t‖ ≤ C * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ))
    (f : V →ₗ[K] V)
    (hf : ∀ v j, ‖b.repr (f v) j‖₊ ≤
      (b.repr v).support.sup (fun k ↦ ‖b.repr v k‖₊))
    (v : V) : ‖f v‖ ≤ (C / c) * ‖v‖ := by
  have hmax : (b.repr (f v)).support.sup (fun j ↦ ‖b.repr (f v) j‖₊) ≤
      (b.repr v).support.sup (fun j ↦ ‖b.repr v j‖₊) :=
    Finset.sup_le (fun j _ ↦ hf v j)
  have hout := (hb (b.repr (f v))).2
  simp only [LinearEquiv.symm_apply_apply] at hout
  calc
    ‖f v‖ ≤ C * (↑((b.repr (f v)).support.sup (fun j ↦ ‖b.repr (f v) j‖₊)) : ℝ) := hout
    _ ≤ C * (↑((b.repr v).support.sup (fun j ↦ ‖b.repr v j‖₊)) : ℝ) :=
      mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hmax) (hc.le.trans hcC)
    _ ≤ C * (c⁻¹ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (max_le_norm b c hc (fun t ↦ (hb t).1) v) (hc.le.trans hcC)
    _ = (C / c) * ‖v‖ := by ring

/-- The bounded coordinate maps and projections exist with their pointwise formulas.

Source: blueprint, sec-six-functors-basics, sk-thm-sf-ctf-stability-direct-images,
paragraph (3), coefficient auxiliary (blueprint: lem-sfb-bounded-coordinate-split-projections).
The proof expands vectors in the algebraic basis, applies the two assumed norm bounds to
finite supports, and uses `AddMonoidHomClass.continuous_of_bound`.
-/
private theorem exists_bounded_coordinate_data
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (J : Type w) (b : Module.Basis J K V) (j₀ : J)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ t : J →₀ K,
      c * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ) ≤ ‖b.repr.symm t‖ ∧
      ‖b.repr.symm t‖ ≤ C * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ)) :
    ∃ (lam : J → V →L[K] K) (E : J → J → V →L[K] V)
      (theta : V → V →L[K] V) (p : Set J → V →L[K] V),
      (∀ j : J, (lam j).toLinearMap = b.coord j) ∧
      (∀ (j : J) (v₀ : V), ‖lam j v₀‖ ≤ c⁻¹ * ‖v₀‖) ∧
      (∀ (i j : J) (v₀ : V),
        E i j v₀ = lam j v₀ • b i ∧ ‖E i j v₀‖ ≤ (C / c) * ‖v₀‖) ∧
      (∀ v₀ w₀ : V,
        theta v₀ w₀ = lam j₀ w₀ • v₀ ∧
        ‖theta v₀ w₀‖ ≤ c⁻¹ * ‖v₀‖ * ‖w₀‖) ∧
      (∀ (A : Set J) (v₀ : V),
        p A v₀ = (b.repr v₀).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j) ∧
        ‖p A v₀‖ ≤ (C / c) * ‖v₀‖) := by
  classical
  have hl (j : J) (v : V) : ‖b.coord j v‖ ≤ c⁻¹ * ‖v‖ :=
    (NNReal.coe_le_coe.mpr (coeff_le_max (b.repr v) j)).trans
      (max_le_norm b c _hc (fun t ↦ (_hb t).1) v)
  let lam (j : J) : V →L[K] K := (b.coord j).mkContinuous c⁻¹ (hl j)
  have hlam (j : J) : (lam j).toLinearMap = b.coord j := rfl
  have hbasis (i : J) : ‖b i‖ ≤ C := by
    simpa [Finsupp.support_single, Basis.repr_symm_single_one] using
      (_hb (Finsupp.single i 1)).2
  let E (i j : J) : V →L[K] V := (lam j).smulRight (b i)
  let theta (v : V) : V →L[K] V := (lam j₀).smulRight v
  let q (A : Set J) : V →ₗ[K] V := b.constr K (A.indicator b)
  have hq (A : Set J) (v : V) :
      q A v = (b.repr v).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j) := by
    rw [show q A v = _ from b.constr_apply K (A.indicator b) v]
    apply Finsupp.sum_congr
    intro j t
    by_cases h : j ∈ A <;> simp [Set.indicator, h]
  have hqcoord (A : Set J) (v : V) (j : J) :
      b.repr (q A v) j = if j ∈ A then b.repr v j else 0 := by
    have heq : (b.coord j).comp (q A) =
        (if j ∈ A then b.coord j else 0) := by
      apply b.ext
      intro k
      by_cases hkj : k = j
      · subst k
        by_cases hj : j ∈ A <;>
          simp [q, hj, Basis.coord_apply, Basis.repr_self, Set.indicator]
      · by_cases hk : k ∈ A <;> by_cases hj : j ∈ A <;>
          simp [q, hk, hj, hkj, Basis.coord_apply, Basis.repr_self, Set.indicator]
    by_cases hj : j ∈ A
    · simpa [Basis.coord_apply, hj] using congrArg (fun f : V →ₗ[K] K ↦ f v) heq
    · simpa [Basis.coord_apply, hj] using congrArg (fun f : V →ₗ[K] K ↦ f v) heq
  have hqbound (A : Set J) (v : V) : ‖q A v‖ ≤ (C / c) * ‖v‖ := by
    apply bound_of_coeff_bound b c C _hc _hcC _hb (q A) _ v
    intro w j
    rw [hqcoord]
    split_ifs
    · exact coeff_le_max _ _
    · simp
  let p (A : Set J) : V →L[K] V := (q A).mkContinuous (C / c) (hqbound A)
  refine ⟨lam, E, theta, p, hlam, hl, ?_, ?_, ?_⟩
  · intro i j v
    refine ⟨rfl, ?_⟩
    change ‖lam j v • b i‖ ≤ _
    rw [norm_smul]
    calc
      ‖lam j v‖ * ‖b i‖ ≤ (c⁻¹ * ‖v‖) * C :=
        mul_le_mul (hl j v) (hbasis i) (norm_nonneg _) (by positivity)
      _ = (C / c) * ‖v‖ := by ring
  · intro v w
    refine ⟨rfl, ?_⟩
    change ‖lam j₀ w • v‖ ≤ _
    rw [norm_smul]
    calc
      ‖lam j₀ w‖ * ‖v‖ ≤ (c⁻¹ * ‖w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hl j₀ w) (norm_nonneg v)
      _ = c⁻¹ * ‖v‖ * ‖w‖ := by ring
  · intro A v
    exact ⟨hq A v, hqbound A v⟩

/-- Continuous split reindexing maps exist with their basis values and bounds.

Source: blueprint, sec-six-functors-basics, sk-thm-sf-ctf-stability-direct-images,
paragraph (3), coefficient auxiliary (blueprint: lem-sfb-bounded-coordinate-split-projections).
The proof constructs finite-support linear maps along `Nat.Subtype.orderIsoOfNat`, then
applies the same norm-bound continuity criterion.
-/
private theorem exists_bounded_reindex_data
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (b : Module.Basis ℕ K V)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ t : ℕ →₀ K,
      c * (↑(t.support.sup (fun n ↦ ‖t n‖₊)) : ℝ) ≤ ‖b.repr.symm t‖ ∧
      ‖b.repr.symm t‖ ≤ C * (↑(t.support.sup (fun n ↦ ‖t n‖₊)) : ℝ))
    (A : Set ℕ) (_hA : A.Infinite) :
    ∃ (a : ℕ ≃o A) (u r p : V →L[K] V),
      (∀ n : ℕ, u (b n) = b (a n : ℕ)) ∧
      (∀ n : ℕ, r (b (a n : ℕ)) = b n) ∧
      (∀ m : ℕ, m ∉ A → r (b m) = 0) ∧
      (∀ v₀ : V,
        p v₀ = (b.repr v₀).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j)) ∧
      (∀ v₀ : V, ‖u v₀‖ ≤ (C / c) * ‖v₀‖ ∧ ‖r v₀‖ ≤ (C / c) * ‖v₀‖) := by
  classical
  let : Infinite A := _hA.to_subtype
  let a : ℕ ≃o A := Nat.Subtype.orderIsoOfNat A
  let f : ℕ → ℕ := fun n ↦ (a n : ℕ)
  have hf : Function.Injective f := Subtype.val_injective.comp a.injective
  let U : V →ₗ[K] V := b.repr.symm.toLinearMap.comp
    ((Finsupp.lmapDomain K K f).comp b.repr.toLinearMap)
  let R : V →ₗ[K] V := b.repr.symm.toLinearMap.comp
    ((Finsupp.lcomapDomain f hf).comp b.repr.toLinearMap)
  have hUcoord (v : V) : b.repr (U v) = Finsupp.mapDomain f (b.repr v) := by
    change b.repr (b.repr.symm (Finsupp.mapDomain f (b.repr v))) = _
    exact b.repr.apply_symm_apply _
  have hRcoord (v : V) (n : ℕ) : b.repr (R v) n = b.repr v (f n) := by
    simp [R]
  have hUb (v : V) : ‖U v‖ ≤ (C / c) * ‖v‖ := by
    apply bound_of_coeff_bound b c C _hc _hcC _hb U _ v
    intro w j
    rw [hUcoord]
    by_cases hj : j ∈ Set.range f
    · obtain ⟨n, rfl⟩ := hj
      rw [Finsupp.mapDomain_apply hf]
      exact coeff_le_max _ _
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hj]
      simp
  have hRb (v : V) : ‖R v‖ ≤ (C / c) * ‖v‖ := by
    apply bound_of_coeff_bound b c C _hc _hcC _hb R _ v
    intro w j
    rw [hRcoord]
    exact coeff_le_max _ _
  let u : V →L[K] V := U.mkContinuous (C / c) hUb
  let r : V →L[K] V := R.mkContinuous (C / c) hRb
  obtain ⟨lam, E, theta, p, hcoord, hl, he, ht, hp⟩ :=
    exists_bounded_coordinate_data K V ℕ b 0 c C _hc _hcC _hb
  refine ⟨a, u, r, p A, ?_, ?_, ?_, fun v ↦ (hp A v).1, ?_⟩
  · intro n
    apply b.repr.injective
    change b.repr (U (b n)) = _
    rw [hUcoord]
    simp [Basis.repr_self, f]
  · intro n
    apply b.repr.injective
    ext j
    change b.repr (R (b (a n : ℕ))) j = _
    rw [hRcoord]
    rw [b.repr_self, b.repr_self]
    change (Finsupp.single (f n) (1 : K)) (f j) = (Finsupp.single n (1 : K)) j
    simp only [Finsupp.single_apply, hf.eq_iff]
  · intro m hm
    apply b.repr.injective
    ext j
    change b.repr (R (b m)) j = _
    rw [hRcoord]
    have hne : m ≠ f j := fun h ↦ hm (h.symm ▸ (a j).property)
    simp [Basis.repr_self, hne]
  · intro v
    exact ⟨hUb v, hRb v⟩


/-- Algebraic identities for the coordinate data, obtained by evaluating on finite-support
expansions and using uniqueness of basis coordinates.

Source: blueprint, sec-six-functors-basics, sk-thm-sf-ctf-stability-direct-images,
paragraph (3) (blueprint: lem-sfb-bounded-coordinate-split-projections).
-/
private theorem coordinate_data_identities
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (J : Type w) (b : Module.Basis J K V) (j₀ : J)
    (lam : J → V →L[K] K) (E : J → J → V →L[K] V)
    (p : Set J → V →L[K] V)
    (hlam : ∀ j : J, (lam j).toLinearMap = b.coord j)
    (hE : ∀ (i j : J) (v : V), E i j v = lam j v • b i)
    (hp : ∀ (A : Set J) (v : V),
      p A v = (b.repr v).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j)) :
    (∀ i j k l : J,
      (j = k → E i j * E k l = E i l) ∧
      (j ≠ k → E i j * E k l = 0)) ∧
    (∀ A B : Set J, p A * p B = p (A ∩ B)) ∧
    (∀ (A B : Set J) (hF : (A ∩ B).Finite),
      p A * p B = ∑ k ∈ hF.toFinset, E k k ∧
      p A * p B = ∑ k ∈ hF.toFinset, E k j₀ * E j₀ j₀ * E j₀ k) := by
  classical
  have hl (j : J) (v : V) : lam j v = b.repr v j :=
    congrArg (fun f : V →ₗ[K] K ↦ f v) (hlam j)
  have hpb (A : Set J) (j : J) : p A (b j) = if j ∈ A then b j else 0 := by
    rw [hp]
    simp [Basis.repr_self, Set.indicator]
  have hmat : ∀ i j k l : J,
      (j = k → E i j * E k l = E i l) ∧
      (j ≠ k → E i j * E k l = 0) := by
    intro i j k l
    constructor
    · intro h
      subst k
      ext v
      simp [hE, hl, map_smul, Basis.repr_self]
    · intro h
      ext v
      simp [hE, hl, map_smul, Basis.repr_self, h]
  have hinter (A B : Set J) : p A * p B = p (A ∩ B) := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    change p A (p B (b j)) = p (A ∩ B) (b j)
    by_cases hA : j ∈ A <;> by_cases hB : j ∈ B <;> simp [hpb, hA, hB]
  refine ⟨hmat, hinter, ?_⟩
  intro A B hF
  have hsum : p A * p B = ∑ k ∈ hF.toFinset, E k k := by
    rw [hinter]
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    change p (A ∩ B) (b j) = (∑ k ∈ hF.toFinset, E k k) (b j)
    simp only [sum_apply, hE, hl, Basis.repr_self_apply]
    by_cases hj : j ∈ A ∩ B
    · simp [hpb, hj, hF.mem_toFinset]
    · simp [hpb, hj, hF.mem_toFinset]
  refine ⟨hsum, ?_⟩
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(hmat k j₀ j₀ j₀).1 rfl, (hmat k j₀ j₀ k).1 rfl]


/-- Split reindexing identities follow from the displayed basis values and projection formula.

Source: blueprint, sec-six-functors-basics, sk-thm-sf-ctf-stability-direct-images,
paragraph (3) (blueprint: lem-sfb-bounded-coordinate-split-projections).
-/
private theorem reindex_data_identities
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (b : Module.Basis ℕ K V)
    (A : Set ℕ)
    (a : ℕ ≃o A) (u r p : V →L[K] V)
    (hu : ∀ n : ℕ, u (b n) = b (a n : ℕ))
    (hr : ∀ n : ℕ, r (b (a n : ℕ)) = b n)
    (hro : ∀ m : ℕ, m ∉ A → r (b m) = 0)
    (hp : ∀ v : V, p v = (b.repr v).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j)) :
    r * u = 1 ∧ u * r = p ∧ p * u = u := by
  classical
  have hpb (j : ℕ) : p (b j) = if j ∈ A then b j else 0 := by
    rw [hp]
    simp [Basis.repr_self, Set.indicator]
  constructor
  · apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro n
    change r (u (b n)) = b n
    rw [hu, hr]
  constructor
  · apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro m
    change u (r (b m)) = p (b m)
    by_cases hm : m ∈ A
    · obtain ⟨n, hn⟩ := a.surjective ⟨m, hm⟩
      have hn' : (a n : ℕ) = m := congrArg Subtype.val hn
      rw [← hn', hr, hu, hpb, if_pos (a n).property]
    · simp [hro m hm, hpb, hm]
  · apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro n
    change p (u (b n)) = u (b n)
    rw [hu, hpb, if_pos (a n).property]



/-- Uniform two-sided coordinate bounds give the continuous coordinate operators and
all finite overlap identities.

Source: blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary,
returned reconstruction proof steps 1 and 5--7
(blueprint: lem-sfb-bounded-coordinate-split-projections).

Proof:
1. For the unique finite expansion of v, let m(v) be the maximum coefficient norm,
   with m(0) = 0. The lower bound gives norm(lambda_j(v)) <= m(v) <= c^(-1) norm(v).
   The upper bound applied to a singleton coefficient 1 gives norm(b_i) <= C.
2. Define E_ij(v) = lambda_j(v) b_i and theta_v(w) = lambda_j0(w) v. Coordinates are
   linear by uniqueness of expansion. Norm homogeneity gives the displayed bounds.
   Apply AddMonoidHomClass.continuous_of_bound, the declaration of
   lem-sfb-additive-norm-bound-continuity, to coordinates, matrix units and theta_v.
3. Evaluate E_ij E_kl on a vector. Since lambda_j(b_k) is 1 for j = k and 0 otherwise,
   the result is precisely the asserted Kronecker-delta multiplication rule.
4. Define p_A by deleting coordinates outside A in the finite expansion. This is linear,
   and m(p_A(v)) <= m(v). Apply the upper bound to the output and the lower bound to
   the input to get norm(p_A(v)) <= (C/c) norm(v). The same continuity lemma applies.
5. The coordinates of p_A p_B are exactly those in A intersect B. For a finite
   intersection, evaluation on v gives the sum of E_kk. The multiplication rule gives
   E_kj0 E_j0j0 E_j0k = E_kk term by term. An empty intersection gives the zero map.

`V →L[K] V` has composition as multiplication. The two implications in the matrix-unit
clause express the Kronecker delta without a decidable-equality assumption on J.
The indicator in the projection formula merely deletes coordinates outside A. -/
theorem bounded_coordinate_split_projections
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (J : Type w) (b : Module.Basis J K V) (j₀ : J)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ t : J →₀ K,
      c * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ) ≤ ‖b.repr.symm t‖ ∧
      ‖b.repr.symm t‖ ≤ C * (↑(t.support.sup (fun j ↦ ‖t j‖₊)) : ℝ)) :
    ∃ (lam : J → V →L[K] K) (E : J → J → V →L[K] V)
      (theta : V → V →L[K] V) (p : Set J → V →L[K] V),
      (∀ j : J, (lam j).toLinearMap = b.coord j) ∧
      (∀ (j : J) (v₀ : V), ‖lam j v₀‖ ≤ c⁻¹ * ‖v₀‖) ∧
      (∀ (i j : J) (v₀ : V),
        E i j v₀ = lam j v₀ • b i ∧ ‖E i j v₀‖ ≤ (C / c) * ‖v₀‖) ∧
      (∀ i j k l : J,
        (j = k → E i j * E k l = E i l) ∧
        (j ≠ k → E i j * E k l = 0)) ∧
      (∀ v₀ w₀ : V,
        theta v₀ w₀ = lam j₀ w₀ • v₀ ∧
        ‖theta v₀ w₀‖ ≤ c⁻¹ * ‖v₀‖ * ‖w₀‖) ∧
      (∀ (A : Set J) (v₀ : V),
        p A v₀ = (b.repr v₀).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j) ∧
        ‖p A v₀‖ ≤ (C / c) * ‖v₀‖) ∧
      (∀ A B : Set J, p A * p B = p (A ∩ B)) ∧
      (∀ (A B : Set J) (hF : (A ∩ B).Finite),
        p A * p B = ∑ k ∈ hF.toFinset, E k k ∧
        p A * p B = ∑ k ∈ hF.toFinset, E k j₀ * E j₀ j₀ * E j₀ k) := by
  obtain ⟨lam, E, theta, p, hlam, hlam_bound, hE, htheta, hp⟩ :=
    exists_bounded_coordinate_data K V J b j₀ c C _hc _hcC _hb
  obtain ⟨hmat, hinter, hfin⟩ :=
    coordinate_data_identities K V J b j₀ lam E p hlam
      (fun i j v ↦ (hE i j v).1) (fun A v ↦ (hp A v).1)
  exact ⟨lam, E, theta, p, hlam, hlam_bound, hE, hmat, htheta, hp, hinter, hfin⟩

/-- On a natural-number basis, every infinite coordinate subset admits bounded split
reindexings along an increasing bijection.

Source: blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary,
returned reconstruction proof steps 5--7
(blueprint: lem-sfb-bounded-coordinate-split-projections).

Proof:
6. Use Nat.Subtype.orderIsoOfNat, the declaration of
   lem-sfb-infinite-nat-increasing-enumeration, to enumerate the infinite subset A in
   increasing order. Extend b_n |-> b_a(n) linearly to u; extend b_a(n) |-> b_n and
   b_m |-> 0 outside A linearly to r. These use only finite basis expansions. Let p
   be the coordinate projection constructed in steps 1--5 of the preceding theorem.
   On each basis vector, r u = 1, u r = p, and p u = u, so the same holds on V.
7. The injective reindexing u preserves the maximum coefficient norm. Deleting the
   coordinates outside A and reindexing with the inverse bijection cannot increase
   that maximum. Apply the upper norm bound to each output and the lower bound to
   its input. Both operators have pointwise bound C/c; apply
   AddMonoidHomClass.continuous_of_bound (lem-sfb-additive-norm-bound-continuity).
   All three identities therefore hold in the continuous endomorphism algebra.

The order isomorphism is exactly a strictly increasing bijection onto A. The displayed
formula fixes p to be the same coordinate projection as in the general-index statement;
it is independent of the distinguished index j₀ used only for the rank-one formulas. -/
theorem bounded_coordinate_split_reindexing
    (K : Type u) [NormedField K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace K V]
    (b : Module.Basis ℕ K V)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ t : ℕ →₀ K,
      c * (↑(t.support.sup (fun n ↦ ‖t n‖₊)) : ℝ) ≤ ‖b.repr.symm t‖ ∧
      ‖b.repr.symm t‖ ≤ C * (↑(t.support.sup (fun n ↦ ‖t n‖₊)) : ℝ))
    (A : Set ℕ) (_hA : A.Infinite) :
    ∃ (a : ℕ ≃o A) (u r p : V →L[K] V),
      (∀ n : ℕ, u (b n) = b (a n : ℕ)) ∧
      (∀ n : ℕ, r (b (a n : ℕ)) = b n) ∧
      (∀ m : ℕ, m ∉ A → r (b m) = 0) ∧
      (∀ v₀ : V,
        p v₀ = (b.repr v₀).sum (fun j t ↦ A.indicator (fun k ↦ t • b k) j)) ∧
      r * u = 1 ∧ u * r = p ∧ p * u = u ∧
      (∀ v₀ : V, ‖u v₀‖ ≤ (C / c) * ‖v₀‖ ∧ ‖r v₀‖ ≤ (C / c) * ‖v₀‖) := by
  obtain ⟨a, u, r, p, hu, hr, hro, hp, hbound⟩ :=
    exists_bounded_reindex_data K V b c C _hc _hcC _hb A _hA
  obtain ⟨hru, hur, hpu⟩ := reindex_data_identities K V b A a u r p hu hr hro hp
  exact ⟨a, u, r, p, hu, hr, hro, hp, hru, hur, hpu, hbound⟩

end Module.Basis
