/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Topology.ProfiniteCechTuples
import Sheaf.Topology.FiniteValuedCechCocycleDescent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Lifting finite-coefficient Cech primitives with prescribed reduction

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2), (4),
printed p. 33; the explicit finite-kernel correction formulated in the DAG
(blueprint: lem-sfb-finite-coefficient-cech-primitive-lift).

The equations are pointwise alternating sums on the existing equal-image tuple spaces.
No section of the profinite surjection or additive section of the coefficient map is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped BigOperators

namespace Profinite

open AlgebraicTopology

private def nerveToScalar {S T : Profinite.{v}} (q : C(T, S)) (n : ℕ) :
    C(setCechNerve q n, scalarCechTuples q (n + 1)) :=
  ⟨fun x ↦ ⟨x.val, fun i j ↦ (x.property i).trans (x.property j).symm⟩,
    continuous_subtype_val.subtype_mk _⟩

private def scalarToNerve {S T : Profinite.{v}} (q : C(T, S)) (n : ℕ) :
    C(scalarCechTuples q (n + 1), setCechNerve q n) :=
  ⟨fun x ↦ ⟨x.val, fun i ↦ x.property i 0⟩,
    continuous_subtype_val.subtype_mk _⟩

private def nerveDelete {X Y : Type v} [TopologicalSpace X] (q : X → Y)
    (n : ℕ) (j : Fin (n + 2)) :
    C(setCechNerve q (n + 1), setCechNerve q n) :=
  ⟨setCechFace q j, by
    change Continuous (fun x : setCechNerve q (n + 1) ↦ setCechFace q j x)
    apply Continuous.subtype_mk
    exact continuous_pi fun i ↦ (continuous_apply (j.succAbove i)).comp
      continuous_subtype_val⟩

private def boundary {X Y : Type v} [TopologicalSpace X] (q : X → Y)
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (n : ℕ) (t : C(setCechNerve q n, M)) : C(setCechNerve q (n + 1), M) :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • t.comp (nerveDelete q n j)

private theorem boundary_apply {X Y : Type v} [TopologicalSpace X] (q : X → Y)
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (n : ℕ) (t : C(setCechNerve q n, M)) (x : setCechNerve q (n + 1)) :
    boundary q n t x = ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • t (setCechFace q j x) := by
  simp [boundary, nerveDelete]

private theorem boundary_squared {X Y : Type v} [TopologicalSpace X] (q : X → Y)
    (hq : Function.Surjective q)
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (n : ℕ) (t : C(setCechNerve q n, M)) :
    boundary q (n + 1) (boundary q n t) = 0 := by
  classical
  ext x
  have h := LinearMap.congr_fun ((setCechNerve_free_resolution ℤ q hq).1 n)
    (Finsupp.single x 1)
  have he := congrArg (Finsupp.linearCombination ℤ (fun y ↦ t y)) h
  simpa [setCechDifferential, boundary_apply, Finsupp.linearCombination,
    map_sum, map_smul] using he

private def prepend {X Y : Type v} (q : X → Y) (s : Y → X)
    (hs : ∀ y, q (s y) = y) {n : ℕ} (x : setCechNerve q n) :
    setCechNerve q (n + 1) :=
  ⟨Fin.cons (s (q (x.val 0))) x.val, fun i ↦ Fin.cases rfl
    (fun j ↦ (x.property j).trans (hs (q (x.val 0))).symm) i⟩

private theorem face_prepend_zero {X Y : Type v} (q : X → Y) (s : Y → X)
    (hs : ∀ y, q (s y) = y) {n : ℕ} (x : setCechNerve q n) :
    setCechFace q 0 (prepend q s hs x) = x := by
  apply Subtype.ext
  funext i
  simp [setCechFace, prepend]

private theorem face_prepend_succ {X Y : Type v} (q : X → Y) (s : Y → X)
    (hs : ∀ y, q (s y) = y) {n : ℕ} (x : setCechNerve q (n + 1))
    (j : Fin (n + 2)) :
    setCechFace q j.succ (prepend q s hs x) =
      prepend q s hs (setCechFace q j x) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [setCechFace, prepend, x.property (j.succAbove 0)]
  · simp [setCechFace, prepend, Fin.succ_succAbove_succ]

private theorem finite_primitive
    (T S : Type v) [TopologicalSpace T] [TopologicalSpace S]
    [CompactSpace T] [CompactSpace S] [T2Space T] [T2Space S]
    [TotallyDisconnectedSpace T] [TotallyDisconnectedSpace S]
    (q : C(T, S)) (hq : Function.Surjective q)
    (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (n : ℕ) (c : C(setCechNerve q (n + 1), M))
    (hc : ∀ x : setCechNerve q (n + 2),
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • c (setCechFace q j x) = 0) :
    ∃ w : C(setCechNerve q n, M), boundary q n w = c := by
  classical
  obtain ⟨T₀, S₀, hT, hS, tT, tS, dT, dS, a, b, q₀,
    ha, hb, hq₀, hcomm, c₀, hdesc, hc₀⟩ :=
    Topology.finite_valued_cech_cocycle_descent T S q hq M (n + 1) (by omega) c hc
  let project (k : ℕ) : C(setCechNerve q k, setCechNerve q₀ k) :=
    ⟨fun x ↦ ⟨fun i ↦ a (x.val i), fun i ↦ (hcomm (x.val i)).trans
      ((congrArg b (x.property i)).trans (hcomm (x.val 0)).symm)⟩,
      (continuous_pi fun i ↦ a.continuous.comp
        ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _⟩
  obtain ⟨s, hs⟩ := hq₀.hasRightInverse
  have : DiscreteTopology (setCechNerve q₀ n) := by
    dsimp [setCechNerveTopologicalSpace, setCechNerve]
    infer_instance
  let w₀ : C(setCechNerve q₀ n, M) :=
    ⟨fun x ↦ c₀ (prepend q₀ s hs x), continuous_of_discreteTopology⟩
  refine ⟨w₀.comp (project n), ?_⟩
  ext x
  have h := hc₀ (prepend q₀ s hs (project (n + 1) x))
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, pow_zero, one_smul, face_prepend_zero,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, face_prepend_succ] at h
  rw [Finset.sum_neg_distrib] at h
  rw [boundary_apply, hdesc x]
  have hface (j : Fin (n + 2)) :
      project n (setCechFace q j x) = setCechFace q₀ j (project (n + 1) x) := rfl
  have heq := (eq_neg_iff_add_eq_zero.mpr h)
  simp only [neg_neg] at heq
  simpa only [ContinuousMap.comp_apply, w₀, ContinuousMap.coe_mk, hface, project] using
    heq.symm

private theorem lift_nerve
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q)
    (A : Type u) [AddCommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (B : Type w) [AddCommGroup B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (p : B →+ A) (hp : Function.Surjective p) (n : ℕ)
    (c : C(setCechNerve q (n + 1), B))
    (hc : ∀ x : setCechNerve q (n + 2),
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • c (setCechFace q j x) = 0)
    (u₀ : C(setCechNerve q n, A))
    (hu : ∀ x : setCechNerve q (n + 1),
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • u₀ (setCechFace q j x) = p (c x)) :
    ∃ v₀ : C(setCechNerve q n, B),
      (∀ x, p (v₀ x) = u₀ x) ∧ boundary q n v₀ = c := by
  classical
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  let t : C(setCechNerve q n, B) :=
    (⟨s, continuous_of_discreteTopology⟩ : C(A, B)).comp u₀
  have ht (x : setCechNerve q n) : p (t x) = u₀ x := hs _
  have hdt (x : setCechNerve q (n + 1)) : p (boundary q n t x) = p (c x) := by
    simp only [boundary_apply, map_sum, map_zsmul, ht, hu]
  have hek (x : setCechNerve q (n + 1)) : c x - boundary q n t x ∈ p.ker := by
    change p (c x - boundary q n t x) = 0
    rw [map_sub, hdt, sub_self]
  let e : C(setCechNerve q (n + 1), p.ker) :=
    ⟨fun x ↦ ⟨c x - boundary q n t x, hek x⟩,
      (c.continuous.sub (boundary q n t).continuous).subtype_mk hek⟩
  have he (x : setCechNerve q (n + 2)) :
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • e (setCechFace q j x) = 0 := by
    apply Subtype.ext
    have hd := congrArg (fun f : C(setCechNerve q (n + 2), B) ↦ f x)
      (boundary_squared q hq n t)
    simp only [boundary_apply, ContinuousMap.zero_apply] at hd
    change (p.ker.subtype) (∑ j : Fin (n + 3),
      (-1 : ℤ) ^ j.val • e (setCechFace q j x)) = 0
    simp only [map_sum, map_zsmul]
    change (∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val •
      (c (setCechFace q j x) - boundary q n t (setCechFace q j x))) = 0
    simp only [smul_sub, Finset.sum_sub_distrib, hc, boundary_apply, hd, sub_self]
  obtain ⟨w, hw⟩ := finite_primitive T S q hq p.ker n e he
  let iw : C(setCechNerve q n, B) :=
    ⟨fun x ↦ (w x).val, continuous_subtype_val.comp w.continuous⟩
  refine ⟨t + iw, ?_, ?_⟩
  · intro x
    change p (t x + (w x).val) = u₀ x
    rw [map_add, ht, (w x).property, add_zero]
  · ext x
    have hwx := congrArg (fun f : C(setCechNerve q (n + 1), p.ker) ↦ (f x).val) hw
    change (p.ker.subtype) (boundary q n w x) = c x - boundary q n t x at hwx
    simp only [boundary_apply, map_sum, map_zsmul] at hwx
    simp only [boundary_apply, ContinuousMap.add_apply, smul_add, Finset.sum_add_distrib]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • t (setCechFace q j x)) +
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • (w (setCechFace q j x)).val) = c x
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (w (setCechFace q j x)).val) =
        c x - ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • t (setCechFace q j x) at hwx
    rw [hwx]
    abel

/-- A prescribed primitive modulo a finite coefficient quotient lifts to a primitive.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2), (4),
printed p. 33; agent-formulated pointwise Cech lemma and finite-kernel correction
(blueprint: lem-sfb-finite-coefficient-cech-primitive-lift).

Proof: (1) For the empty surjection all positive-length tuple spaces are empty, so
all cochains vanish. In general deletion maps are continuous, the two orders of
coordinate deletion cancel with opposite signs, and additive coefficient maps commute
with the signed sums. Thus d squared is zero. (2) Choose a set section s of p, which
is continuous because A and B are discrete, and lift u₀ to t = s composed with u₀.
The difference e = c - d t takes values in the finite discrete kernel K of p and is
a continuous K-valued cocycle. (3) Apply lem-sfb-finite-valued-cech-cocycle-descent to
e in degree n. It descends, together with its cocycle equation on every quotient
tuple, to a finite discrete surjection q₀ : T₀ → S₀ and a K-valued cocycle e₀.
(4) Choose a section of q₀ and insert its value at the common base image as the first
coordinate of e₀. Evaluating the cocycle equation on the resulting tuple shows that
this finite, hence continuous, cochain w₀ satisfies d w₀ = e₀. Here n ≥ 1 ensures that
after deleting the first original coordinate another coordinate remains with the same
base image. (5) Pull w₀ back along the finite quotient map to obtain w with d w = e.
Then v₀ = t + w, with the kernel inclusion understood, satisfies p v₀ = u₀ and d v₀ = c.
This includes zero coefficient groups; A = 0 gives a primitive for every cocycle. -/
theorem finite_coefficient_cech_primitive_lift
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q)
    (A : Type u) [AddCommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (B : Type w) [AddCommGroup B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (p : B →+ A) (hp : Function.Surjective p) (n : ℕ) (hn : 1 ≤ n)
    (c : C(scalarCechTuples q (n + 1), B))
    (hc : ∀ x : scalarCechTuples q (n + 2),
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • c (scalarCechDelete q (n + 1) j x) = 0)
    (u₀ : C(scalarCechTuples q n, A))
    (hu : ∀ x : scalarCechTuples q (n + 1),
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val • u₀ (scalarCechDelete q n j x) = p (c x)) :
    ∃ v₀ : C(scalarCechTuples q n, B),
      (∀ x : scalarCechTuples q n, p (v₀ x) = u₀ x) ∧
      (∀ x : scalarCechTuples q (n + 1),
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val • v₀ (scalarCechDelete q n j x) = c x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨v, hv, hdv⟩ := lift_nerve S T q hq A B p hp k
    (c.comp (nerveToScalar q (k + 1)))
    (fun x ↦ hc (nerveToScalar q (k + 2) x))
    (u₀.comp (nerveToScalar q k))
    (fun x ↦ hu (nerveToScalar q (k + 1) x))
  refine ⟨v.comp (scalarToNerve q k), ?_, ?_⟩
  · intro x
    exact hv (scalarToNerve q k x)
  · intro x
    simpa only [boundary_apply, ContinuousMap.comp_apply, scalarToNerve,
      nerveToScalar, ContinuousMap.coe_mk, scalarCechDelete, setCechFace] using
      congrArg (fun f ↦ f (scalarToNerve q (k + 1) x)) hdv

end Profinite
