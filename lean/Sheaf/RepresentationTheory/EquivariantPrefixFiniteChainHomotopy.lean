/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible

import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # Equivariant prefix homotopy with finite integral evaluations

Source: blueprint, six-functors-basics, ctf-stability direct-images proof (3),
agent auxiliary expansion, prefix comparison (not asserted by the blueprint).
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy)

The index `r` is tuple length, hence chain degree `r - 1`. Length zero is the
single empty tuple. Below degree -1 the complex is extended by zero; the
boundary out of length zero and prefixes out of the lower zero groups are zero.
All constructions are over the integers, with no coefficient object or topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Algebra

/-- Free integral tuple chains, including the unique empty tuple at length zero.
Source: auxiliary expansion in direct-images (3).
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
abbrev prefixChains (G : Type u) (r : ℕ) := (Fin r → G) →₀ ℤ

/-- Alternating deletion, including the augmentation at `r = 0`.
This is the existing power-set differential with the augmentation target written
as the free group on the empty tuple. Source: direct-images (3), prefix comparison.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
noncomputable def prefixBoundary (G : Type u) :
    (r : ℕ) → prefixChains G (r + 1) →ₗ[ℤ] prefixChains G r
  | 0 => (Finsupp.lsingle (fun i : Fin 0 ↦ Fin.elim0 i)).comp
      (powerSetComplexAugmentation ℤ G)
  | r + 1 => powerSetComplexDifferential ℤ G r

/-- Prefixing a vertex, also sending the empty tuple to the one-vertex tuple.
Source: direct-images (3), prefix comparison; the power-set insertion formula.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
noncomputable def prefixCone (G : Type u) (b : G) :
    (r : ℕ) → prefixChains G r →ₗ[ℤ] prefixChains G (r + 1)
  | 0 => (Finsupp.lift _ _ _) (fun _ ↦ powerSetComplexAugmentationHomotopy ℤ G b 1)
  | r + 1 => powerSetComplexHomotopy ℤ G b r

/-- Diagonal left translation, fixing the empty tuple.
Source: direct-images (3), prefix comparison.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
noncomputable def prefixTranslate (G : Type u) [Group G] (h : G) (r : ℕ) :
    prefixChains G r →ₗ[ℤ] prefixChains G r :=
  Finsupp.lmapDomain ℤ ℤ (fun x i ↦ h * x i)

/-- Recursive prefix homotopy on the last degree of a finite initial segment.
At length zero it is zero. At the next length restrict the given maps to the
previous segment, form the correction on each basis tuple, and prefix its first
coordinate before extending linearly. No map above the last degree is used.
Source: direct-images (3), prefix comparison, recursion.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
noncomputable def prefixRecursiveQ (G : Type u) :
    (r : ℕ) → (∀ p : Fin (r + 1), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val) →
      prefixChains G r →ₗ[ℤ] prefixChains G (r + 1)
  | 0, _ => 0
  | r + 1, A => (Finsupp.lift _ _ _) (fun x ↦
      prefixCone G (x 0) (r + 1)
        (Finsupp.single x (1 : ℤ) -
          A ⟨r + 1, Nat.lt_succ_self _⟩ (Finsupp.single x (1 : ℤ)) -
          prefixRecursiveQ G r (fun p ↦ A p.castSucc)
            (prefixBoundary G r (Finsupp.single x (1 : ℤ)))))

/-- The explicit uncollected formula list for Q on a finite initial segment.
The list at length zero is empty. The next list concatenates the identity term,
the negative A terms, and the signed deleted previous Q terms, each prefixed by
input coordinate zero. The construction never compares values in G and retains
repetitions. Source: direct-images (3), prefix comparison, finite-list induction.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
def prefixFormulaList (G : Type u) :
    (r : ℕ) → (∀ p : Fin r,
      List (ℤ × ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G)))) →
      List (ℤ × ((Fin r → G) → (Fin (r + 1) → G)))
  | 0, _ => []
  | r + 1, b =>
      [((1 : ℤ), fun x : Fin (r + 1) → G ↦ Fin.cons (x 0) x)] ++
      (b (Fin.last r)).map (fun e ↦ (-e.1, fun x : Fin (r + 1) → G ↦ Fin.cons (x 0) (e.2 x))) ++
      (List.finRange (r + 1)).flatMap (fun i ↦
        (prefixFormulaList G r (fun p ↦ b p.castSucc)).map (fun e ↦
          (-((-1 : ℤ) ^ i.val) * e.1,
            fun x ↦ Fin.cons (x 0) (e.2 (fun j ↦ x (i.succAbove j))))))

/-- A fixed coordinate formula using an input coordinate, optionally followed
by rho and a fixed right translation. Choices are uniform in the input tuple.
Source: direct-images (3), prefix comparison, coordinate assertion.
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy) -/
def HasPrefixCoordinates {G : Type u} [Group G] (H : Subgroup G) {ι : Type v}
    (ρ : G → H) (a : ι → G) {r s : ℕ} (f : (Fin r → G) → (Fin s → G)) : Prop :=
  ∀ j : Fin s, ∃ k : Fin r,
    (∀ x, f x j = x k) ∨ ∃ i : ι, ∀ x, f x j = (ρ (x k) : G) * a i

private theorem integral_ext {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : (ι →₀ ℤ) →ₗ[ℤ] M}
    (h : ∀ x, f (Finsupp.single x 1) = g (Finsupp.single x 1)) : f = g := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  exact h x

private theorem prefix_cone_single (G : Type u) (c : G) (r : ℕ)
    (x : Fin r → G) :
    prefixCone G c r (Finsupp.single x 1) = Finsupp.single (Fin.cons c x) 1 := by
  cases r with
  | zero =>
    have hx : (fun _ : Fin 1 ↦ c) = Fin.cons c x := by
      funext i
      fin_cases i
      rfl
    simp [prefixCone, powerSetComplexAugmentationHomotopy, hx]
  | succ r => simp [prefixCone, powerSetComplexHomotopy]

private theorem prefix_boundary_single (G : Type u) (r : ℕ)
    (x : Fin (r + 1) → G) :
    prefixBoundary G r (Finsupp.single x 1) =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
        Finsupp.single (fun j ↦ x (i.succAbove j)) 1 := by
  cases r with
  | zero =>
    have hx : (fun i : Fin 0 ↦ Fin.elim0 i) =
        (fun j : Fin 0 ↦ x ((0 : Fin 1).succAbove j)) := Subsingleton.elim _ _
    simp [prefixBoundary, powerSetComplexAugmentation, hx]
  | succ r =>
    simp only [prefixBoundary, powerSetComplexDifferential, Finsupp.lift_apply,
      Finsupp.sum_single_index, zero_smul, one_smul]
    rfl

private theorem prefix_translate_single (G : Type u) [Group G] (h : G) (r : ℕ)
    (x : Fin r → G) :
    prefixTranslate G h r (Finsupp.single x 1) =
      Finsupp.single (fun i ↦ h * x i) 1 := by
  simp [prefixTranslate]

private theorem prefix_recursive_single (G : Type u) (r : ℕ)
    (A : ∀ p : Fin (r + 2), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val)
    (x : Fin (r + 1) → G) :
    prefixRecursiveQ G (r + 1) A (Finsupp.single x 1) =
      prefixCone G (x 0) (r + 1)
        (Finsupp.single x 1 - A ⟨r + 1, Nat.lt_succ_self _⟩ (Finsupp.single x 1) -
          prefixRecursiveQ G r (fun p ↦ A p.castSucc)
            (prefixBoundary G r (Finsupp.single x 1))) := by
  simp [prefixRecursiveQ]

private theorem prefix_boundary_sq (G : Type u) (r : ℕ) :
    (prefixBoundary G r).comp (prefixBoundary G (r + 1)) = 0 := by
  cases r with
  | zero =>
    have h := (powerSetComplex_basic_identities ℤ G).2.1
    rw [prefixBoundary, prefixBoundary, LinearMap.comp_assoc, h]
    simp
  | succ r => exact (powerSetComplex_basic_identities ℤ G).1 r

private theorem prefix_contraction_zero (G : Type u) (c : G) :
    (prefixBoundary G 0).comp (prefixCone G c 0) = LinearMap.id := by
  apply integral_ext
  intro x
  rw [LinearMap.comp_apply, prefix_cone_single, prefix_boundary_single]
  simp

private theorem prefix_contraction (G : Type u) (c : G) (r : ℕ) :
    (prefixBoundary G (r + 1)).comp (prefixCone G c (r + 1)) +
      (prefixCone G c r).comp (prefixBoundary G r) = LinearMap.id := by
  cases r with
  | zero =>
    apply integral_ext
    intro x
    have h := LinearMap.congr_fun (powerSetComplex_homotopy_identities ℤ G c).2.1
      (Finsupp.single x 1)
    simpa [prefixBoundary, prefixCone, powerSetComplexAugmentation,
      powerSetComplexAugmentationHomotopy] using h
  | succ r => exact (powerSetComplex_homotopy_identities ℤ G c).2.2 r

private theorem prefix_cone_translate (G : Type u) [Group G] (h c : G) (r : ℕ)
    (z : prefixChains G r) :
    prefixTranslate G h (r + 1) (prefixCone G c r z) =
      prefixCone G (h * c) r (prefixTranslate G h r z) := by
  have he : (fun x : Fin r → G ↦ (fun i : Fin (r + 1) ↦ h * (Fin.cons c x : Fin (r + 1) → G) i)) =
      (fun x : Fin r → G ↦ Fin.cons (h * c) (fun i ↦ h * x i)) := by
    funext x i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hm : (prefixTranslate G h (r + 1)).comp (prefixCone G c r) =
      (prefixCone G (h * c) r).comp (prefixTranslate G h r) := by
    apply integral_ext
    intro x
    simp only [LinearMap.comp_apply, prefix_cone_single, prefix_translate_single]
    exact congrArg (fun f ↦ Finsupp.single f (1 : ℤ)) (congrFun he x)
  exact LinearMap.congr_fun hm z

private theorem prefix_boundary_translate (G : Type u) [Group G] (h : G) (r : ℕ)
    (z : prefixChains G (r + 1)) :
    prefixBoundary G r (prefixTranslate G h (r + 1) z) =
      prefixTranslate G h r (prefixBoundary G r z) := by
  have hm : (prefixBoundary G r).comp (prefixTranslate G h (r + 1)) =
      (prefixTranslate G h r).comp (prefixBoundary G r) := by
    apply integral_ext
    intro x
    simp only [LinearMap.comp_apply, prefix_translate_single, prefix_boundary_single,
      map_sum, map_smul, prefix_translate_single]
  exact LinearMap.congr_fun hm z

private theorem prefix_recursive_identity (G : Type u) (r : ℕ)
    (A : ∀ p : Fin (r + 2), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val)
    (haug : A 0 = LinearMap.id)
    (hchain : ∀ p : Fin (r + 1),
      (prefixBoundary G p.val).comp (A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩) =
        (A p.castSucc).comp (prefixBoundary G p.val)) :
    (∀ z : prefixChains G (r + 1),
      prefixBoundary G r (z - A ⟨r + 1, Nat.lt_succ_self _⟩ z -
        prefixRecursiveQ G r (fun j ↦ A j.castSucc) (prefixBoundary G r z)) = 0) ∧
    (LinearMap.id - A ⟨r + 1, Nat.lt_succ_self _⟩ =
      (prefixBoundary G (r + 1)).comp (prefixRecursiveQ G (r + 1) A) +
        (prefixRecursiveQ G r (fun j ↦ A j.castSucc)).comp (prefixBoundary G r)) := by
  have hcycle : ∀ z : prefixChains G (r + 1),
      prefixBoundary G r (z - A ⟨r + 1, Nat.lt_succ_self _⟩ z -
        prefixRecursiveQ G r (fun j ↦ A j.castSucc) (prefixBoundary G r z)) = 0 := by
    cases r with
    | zero =>
      intro z
      have hc := LinearMap.congr_fun (hchain 0) z
      simp only [LinearMap.comp_apply, Fin.val_zero, Fin.castSucc_zero, haug,
        LinearMap.id_apply] at hc
      change prefixBoundary G 0 (A 1 z) = prefixBoundary G 0 z at hc
      simp only [prefixRecursiveQ, LinearMap.zero_apply, sub_zero, map_sub]
      exact sub_eq_zero.mpr hc.symm
    | succ r =>
      intro z
      have hp := prefix_recursive_identity G r (fun p ↦ A p.castSucc) haug
        (fun p ↦ hchain p.castSucc)
      have hc := LinearMap.congr_fun (hchain ⟨r + 1, Nat.lt_succ_self _⟩) z
      have hh := LinearMap.congr_fun hp.2 (prefixBoundary G (r + 1) z)
      have hd := LinearMap.congr_fun (prefix_boundary_sq G r) z
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.add_apply,
        LinearMap.comp_apply, hd, map_zero, add_zero] at hh
      change prefixBoundary G (r + 1) (A ⟨r + 2, by omega⟩ z) =
        A ⟨r + 1, by omega⟩ (prefixBoundary G (r + 1) z) at hc
      simp only [map_sub]
      rw [hc, ← hh]
      exact sub_self _
  refine ⟨hcycle, ?_⟩
  apply integral_ext
  intro x
  have hc := LinearMap.congr_fun (prefix_contraction G (x 0) r)
    (Finsupp.single x 1 - A ⟨r + 1, Nat.lt_succ_self _⟩ (Finsupp.single x 1) -
      prefixRecursiveQ G r (fun j ↦ A j.castSucc)
        (prefixBoundary G r (Finsupp.single x 1)))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hcycle, map_zero, add_zero] at hc
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.add_apply,
    LinearMap.comp_apply, prefix_recursive_single]
  rw [hc]
  abel

private theorem prefix_recursive_equivariant (G : Type u) [Group G]
    (H : Subgroup G) (r : ℕ)
    (A : ∀ p : Fin (r + 1), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val)
    (hequiv : ∀ (p : Fin (r + 1)) (h : H) (z : prefixChains G p.val),
      A p (prefixTranslate G h p.val z) = prefixTranslate G h p.val (A p z))
    (h : H) (z : prefixChains G r) :
    prefixRecursiveQ G r A (prefixTranslate G h r z) =
      prefixTranslate G h (r + 1) (prefixRecursiveQ G r A z) := by
  induction r with
  | zero => simp [prefixRecursiveQ]
  | succ r ih =>
    have hm : (prefixRecursiveQ G (r + 1) A).comp (prefixTranslate G h (r + 1)) =
        (prefixTranslate G h (r + 2)).comp (prefixRecursiveQ G (r + 1) A) := by
      apply integral_ext
      intro x
      simp only [LinearMap.comp_apply, prefix_translate_single, prefix_recursive_single]
      rw [prefix_cone_translate]
      congr 1
      rw [map_sub, map_sub,
        ← hequiv ⟨r + 1, Nat.lt_succ_self _⟩ h (Finsupp.single x 1),
        ← ih (fun p ↦ A p.castSucc) (fun p ↦ hequiv p.castSucc)]
      rw [← prefix_boundary_translate]
      simp only [prefix_translate_single]
    exact LinearMap.congr_fun hm z

private theorem prefix_list_continuous (G : Type u) [TopologicalSpace G] (r : ℕ)
    (b : ∀ p : Fin r,
      List (ℤ × ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G))))
    (hb : ∀ p e, e ∈ b p → Continuous e.2) :
    ∀ e ∈ prefixFormulaList G r b, Continuous e.2 := by
  induction r with
  | zero => simp [prefixFormulaList]
  | succ r ih =>
    intro e he
    simp only [prefixFormulaList, List.mem_append, List.mem_singleton, List.mem_map,
      List.mem_flatMap] at he
    rcases he with (rfl | ⟨e, he, rfl⟩) | ⟨i, _, e, he, rfl⟩
    · exact Continuous.finCons (A := fun _ : Fin (r + 2) ↦ G) (continuous_apply 0) continuous_id
    · exact Continuous.finCons (A := fun _ : Fin (r + 2) ↦ G) (continuous_apply 0)
        (hb (Fin.last r) e he)
    · have hf := ih (fun p ↦ b p.castSucc) (fun p ↦ hb p.castSucc) e he
      exact Continuous.finCons (A := fun _ : Fin (r + 2) ↦ G) (continuous_apply 0)
        (hf.comp (continuous_pi fun j ↦ continuous_apply (i.succAbove j)))

private theorem prefix_coordinates_cons {G : Type u} [Group G] (H : Subgroup G)
    {ι : Type v} (ρ : G → H) (a : ι → G) {r s : ℕ} (k : Fin r)
    (f : (Fin r → G) → (Fin s → G)) (hf : HasPrefixCoordinates H ρ a f) :
    HasPrefixCoordinates H ρ a (fun x ↦ Fin.cons (x k) (f x)) := by
  intro j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · exact ⟨k, Or.inl (fun _ ↦ rfl)⟩
  · simpa only [Fin.cons_succ] using hf j

private theorem prefix_coordinates_select {G : Type u} [Group G] (H : Subgroup G)
    {ι : Type v} (ρ : G → H) (a : ι → G) {r s t : ℕ} (σ : Fin r → Fin t)
    (f : (Fin r → G) → (Fin s → G)) (hf : HasPrefixCoordinates H ρ a f) :
    HasPrefixCoordinates H ρ a (fun x ↦ f (fun j ↦ x (σ j))) := by
  intro j
  rcases hf j with ⟨k, hk | ⟨i, hi⟩⟩
  · exact ⟨σ k, Or.inl (fun x ↦ hk (fun j ↦ x (σ j)))⟩
  · exact ⟨σ k, Or.inr ⟨i, fun x ↦ hi (fun j ↦ x (σ j))⟩⟩

private theorem prefix_list_coordinates {G : Type u} [Group G] (H : Subgroup G)
    {ι : Type v} (ρ : G → H) (a : ι → G) (r : ℕ)
    (b : ∀ p : Fin r,
      List (ℤ × ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G))))
    (hb : ∀ p e, e ∈ b p → HasPrefixCoordinates H ρ a e.2) :
    ∀ e ∈ prefixFormulaList G r b, HasPrefixCoordinates H ρ a e.2 := by
  induction r with
  | zero => simp [prefixFormulaList]
  | succ r ih =>
    intro e he
    simp only [prefixFormulaList, List.mem_append, List.mem_singleton, List.mem_map,
      List.mem_flatMap] at he
    rcases he with (rfl | ⟨e, he, rfl⟩) | ⟨i, _, e, he, rfl⟩
    · exact prefix_coordinates_cons H ρ a 0 _ (fun j ↦ ⟨j, Or.inl (fun _ ↦ rfl)⟩)
    · exact prefix_coordinates_cons H ρ a 0 _ (hb (Fin.last r) e he)
    · apply prefix_coordinates_cons H ρ a 0
      exact prefix_coordinates_select H ρ a i.succAbove _
        (ih (fun p ↦ b p.castSucc) (fun p ↦ hb p.castSucc) e he)

private theorem prefix_sum_flatMap {α M : Type*} [AddCommMonoid M]
    (L : List α) (f : α → List M) :
    (L.flatMap f).sum = (L.map (fun a ↦ (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

private theorem prefix_list_eval (G : Type u) (r : ℕ)
    (A : ∀ p : Fin (r + 1), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val)
    (b : ∀ p : Fin r,
      List (ℤ × ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G))))
    (hA : ∀ (p : Fin r) (x : Fin (p.val + 1) → G),
      A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ (Finsupp.single x (1 : ℤ)) =
        ((b p).map (fun e ↦ e.1 • Finsupp.single (e.2 x) (1 : ℤ))).sum)
    (x : Fin r → G) :
    prefixRecursiveQ G r A (Finsupp.single x 1) =
      ((prefixFormulaList G r b).map
        (fun e ↦ e.1 • Finsupp.single (e.2 x) (1 : ℤ))).sum := by
  induction r with
  | zero => simp [prefixRecursiveQ, prefixFormulaList]
  | succ r ih =>
    rw [prefix_recursive_single, hA ⟨r, Nat.lt_succ_self _⟩ x, prefix_boundary_single]
    simp only [map_sum, map_smul]
    simp_rw [ih (fun p ↦ A p.castSucc) (fun p ↦ b p.castSucc)
      (fun p ↦ hA p.castSucc)]
    simp only [map_sub, map_sum, map_list_sum, map_smul, prefix_cone_single]
    simp only [prefixFormulaList, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def,
      List.map_flatMap, prefix_sum_flatMap, add_zero]
    rw [← Fin.sum_univ_def]
    simp only [sub_eq_add_neg, List.sum_neg, ← Finset.sum_neg_distrib, List.smul_sum,
      List.map_map, Function.comp_def, LinearMap.map_smul, prefix_cone_single,
      one_smul, neg_mul, mul_smul, neg_smul]
    simp only [Fin.last]

/-- The prefix homotopy is equivariant, is a chain homotopy from A to the
identity, and has fixed finite integral continuous evaluations.

Source: blueprint direct-images (3), agent auxiliary prefix comparison (not a
claim of the blueprint itself).
(blueprint: lem-sfb-equivariant-prefix-finite-chain-homotopy)

Proof:
1. Extend basis assignments uniquely and linearly in the free modules
   [def-weil-pbc-free-module]. Thus the displayed recursive Q is a homomorphism.
2. Apply lem-weil-pbc-power-set-complex-contractible over Z. Identify its
   augmentation target with the free group on the empty tuple. This gives d^2=0
   and d C_b + C_b d=1, including d[b]=[empty]. Below this the groups are zero.
3. Deletion commutes with left translation and h C_b=C_(hb) h on basis tuples,
   hence on chains; the same assertion holds at the empty tuple.
4. Put D=1-A. Its augmentation component is zero and it commutes with d.
   At length one, Z=D[x] has zero augmentation, so dQ=Z by the prefix identity.
5. Inductively dZ=(D-dQ_previous)d=Q_previous_previous d^2=0; at length two
   the last Q is the zero augmentation component, never an undefined map.
6. The prefix identity then gives dQ=Z, hence 1-A=dQ+Q_previous d on all chains.
   Only the stated initial segment of A is involved.
7. Inductively Z(hx)=hZ(x); the first coordinate becomes hx_0. Prefix naturality
   gives equivariance on basis tuples and therefore on every chain.
8. At length one, list the identity tuple prefixed by x_0 with coefficient 1
   and the given A terms prefixed by x_0 with negated coefficients.
9. At each next length append, for each deletion i and each previous term,
   its deleted-input evaluation prefixed by x_0 with coefficient -(-1)^i t.
   Expanding the recursion proves exactly the list evaluation formula.
10. Projections, deletions, compositions of the given continuous maps, and
    adjoining an input coordinate are continuous, so every listed map is.
11. Deletion replaces each input coordinate by another input coordinate.
    Consequently the optional rho/right-translation coordinate forms persist.
    Lists are constructed over Z before any coefficient group or topology is
    supplied, and no equality test on evaluated tuples occurs.
-/
theorem equivariant_prefix_finite_chain_homotopy
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (n : ℕ)
    (A : ∀ p : Fin (n + 2), prefixChains G p.val →ₗ[ℤ] prefixChains G p.val)
    (haug : A 0 = LinearMap.id)
    (hchain : ∀ p : Fin (n + 1),
      (prefixBoundary G p.val).comp (A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩) =
        (A p.castSucc).comp (prefixBoundary G p.val))
    (hequiv : ∀ (p : Fin (n + 2)) (h : H) (z : prefixChains G p.val),
      A p (prefixTranslate G h p.val z) = prefixTranslate G h p.val (A p z))
    (b : ∀ p : Fin (n + 1),
      List (ℤ × ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G))))
    (hb : ∀ (p : Fin (n + 1)) (e : ℤ ×
      ((Fin (p.val + 1) → G) → (Fin (p.val + 1) → G))), e ∈ b p → Continuous e.2)
    (hA : ∀ (p : Fin (n + 1)) (x : Fin (p.val + 1) → G),
      A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ (Finsupp.single x (1 : ℤ)) =
        ((b p).map (fun e ↦ e.1 • Finsupp.single (e.2 x) (1 : ℤ))).sum) :
    (∀ r : ℕ, (prefixBoundary G r).comp (prefixBoundary G (r + 1)) = 0) ∧
    (∀ c : G, (prefixBoundary G 0).comp (prefixCone G c 0) = LinearMap.id) ∧
    (∀ (c : G) (r : ℕ),
      (prefixBoundary G (r + 1)).comp (prefixCone G c (r + 1)) +
        (prefixCone G c r).comp (prefixBoundary G r) = LinearMap.id) ∧
    (∀ (h c : G) (r : ℕ) (z : prefixChains G r),
      prefixTranslate G h (r + 1) (prefixCone G c r z) =
        prefixCone G (h * c) r (prefixTranslate G h r z)) ∧
    ∀ p : Fin (n + 1),
      (∀ x : Fin (p.val + 1) → G,
        prefixBoundary G p.val
          (Finsupp.single x (1 : ℤ) -
            A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ (Finsupp.single x (1 : ℤ)) -
            prefixRecursiveQ G p.val (fun j ↦ A ⟨j.val, by omega⟩)
              (prefixBoundary G p.val (Finsupp.single x (1 : ℤ)))) = 0) ∧
      (LinearMap.id - A ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ =
        (prefixBoundary G (p.val + 1)).comp
          (prefixRecursiveQ G (p.val + 1) (fun j ↦ A ⟨j.val, by omega⟩)) +
        (prefixRecursiveQ G p.val (fun j ↦ A ⟨j.val, by omega⟩)).comp
          (prefixBoundary G p.val)) ∧
      (∀ (h : H) (z : prefixChains G (p.val + 1)),
        prefixRecursiveQ G (p.val + 1) (fun j ↦ A ⟨j.val, by omega⟩)
            (prefixTranslate G h (p.val + 1) z) =
          prefixTranslate G h (p.val + 2)
            (prefixRecursiveQ G (p.val + 1) (fun j ↦ A ⟨j.val, by omega⟩) z)) ∧
      (∀ x : Fin (p.val + 1) → G,
        prefixRecursiveQ G (p.val + 1) (fun j ↦ A ⟨j.val, by omega⟩)
            (Finsupp.single x (1 : ℤ)) =
          ((prefixFormulaList G (p.val + 1) (fun j ↦ b ⟨j.val, by omega⟩)).map
            (fun e ↦ e.1 • Finsupp.single (e.2 x) (1 : ℤ))).sum) ∧
      (∀ e ∈ prefixFormulaList G (p.val + 1) (fun j ↦ b ⟨j.val, by omega⟩),
        Continuous e.2) ∧
      ∀ (ι : Type v) (ρ : G → H) (a : ι → G), Continuous ρ →
        (∀ (j : Fin (p.val + 1))
          (e : ℤ × ((Fin (j.val + 1) → G) → (Fin (j.val + 1) → G))),
          e ∈ b ⟨j.val, by omega⟩ →
          HasPrefixCoordinates H ρ a e.2) →
        ∀ e ∈ prefixFormulaList G (p.val + 1) (fun j ↦ b ⟨j.val, by omega⟩),
          HasPrefixCoordinates H ρ a e.2 := by
  refine ⟨prefix_boundary_sq G, prefix_contraction_zero G, prefix_contraction G,
    prefix_cone_translate G, ?_⟩
  intro p
  have hi := prefix_recursive_identity G p.val (fun j ↦ A ⟨j.val, by omega⟩) haug
    (fun j ↦ hchain ⟨j.val, by omega⟩)
  refine ⟨fun x ↦ hi.1 (Finsupp.single x 1), hi.2, ?_, ?_, ?_, ?_⟩
  · exact prefix_recursive_equivariant G H (p.val + 1)
      (fun j ↦ A ⟨j.val, by omega⟩) (fun j ↦ hequiv ⟨j.val, by omega⟩)
  · exact prefix_list_eval G (p.val + 1) (fun j ↦ A ⟨j.val, by omega⟩)
      (fun j ↦ b ⟨j.val, by omega⟩) (fun j ↦ hA ⟨j.val, by omega⟩)
  · exact prefix_list_continuous G (p.val + 1) (fun j ↦ b ⟨j.val, by omega⟩)
      (fun j ↦ hb ⟨j.val, by omega⟩)
  · intro ι ρ a _ hc
    exact prefix_list_coordinates H ρ a (p.val + 1) (fun j ↦ b ⟨j.val, by omega⟩) hc

end Algebra
