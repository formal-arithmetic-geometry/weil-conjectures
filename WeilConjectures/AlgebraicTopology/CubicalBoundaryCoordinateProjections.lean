/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.IntegralLatticeCubicalDefs
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Cubical boundary and coordinate projections

Source: Stacks Project, more-algebra.tex, Tag 0623, alternating differential (comparison
only); the agent-written coordinate lemma extracted from the integral lattice contraction,
steps 1, 2, 6 and 8 (blueprint: lem-sfb-cubical-boundary-coordinate-projections).

The lattice cells, boundary, augmentation, origin section and translations are the existing
constructions in `IntegralLatticeCubical`. This module adds the coordinate-reset maps and
states their identities and the decomposition into regular translation modules.
-/

@[expose] public section

set_option autoImplicit false

namespace IntegralLatticeCubical

/-- Reset coordinate `i` of a lattice vector to zero, by subtracting its `i` component.
Source: the displayed formula for rho in the agent-written coordinate lemma, compared with
Stacks Tag 0623 (blueprint: lem-sfb-cubical-boundary-coordinate-projections). -/
def resetCoordinate (r : ℕ) (i : Fin r) (v : Fin r → ℤ) : Fin r → ℤ :=
  v - v i • unitVector r i

/-- Kill cells containing direction `i`, and reset coordinate `i` on the remaining cells.
The free-module extension supplies the actual homomorphism, also in zero groups.
Source: the displayed formula for p in the agent-written coordinate lemma, compared with
Stacks Tag 0623 (blueprint: lem-sfb-cubical-boundary-coordinate-projections). -/
noncomputable def coordinateProjection (r : ℕ) (a : ℤ) (i : Fin r) :
    Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun c ↦
    if i ∈ c.2.val then 0 else cell r a (resetCoordinate r i c.1) c.2.val

/-- Ordered product of the first `k` coordinate projections, with the empty product equal
to the identity. Only `0 ≤ k ≤ r` is used; `take` also defines the expression for larger k.
Source: the formula for P in the agent-written coordinate lemma, compared with Stacks
Tag 0623 (blueprint: lem-sfb-cubical-boundary-coordinate-projections). -/
noncomputable def coordinateProduct (r : ℕ) (a : ℤ) (k : ℕ) :
    Chains r a →ₗ[ℤ] Chains r a :=
  ((List.finRange r).take k).foldr
    (fun i P ↦ (coordinateProjection r a i).comp P) LinearMap.id

private theorem chains_ext {r : ℕ} {a : ℤ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] {f g : Chains r a →ₗ[ℤ] M}
    (h : ∀ (v : Fin r → ℤ) (I : Directions r a),
      f (Finsupp.single (v, I) 1) = g (Finsupp.single (v, I) 1)) : f = g := by
  apply Finsupp.lhom_ext
  rintro ⟨v, I⟩ n
  have hn : Finsupp.single (v, I) n = n • Finsupp.single (v, I) (1 : ℤ) := by
    simp
  rw [hn, LinearMap.map_smul, LinearMap.map_smul, h]

private theorem cell_valid {r : ℕ} {a : ℤ} (v : Fin r → ℤ) (I : Directions r a) :
    cell r a v I.val = Finsupp.single (v, I) 1 := by
  simp [cell, I.property]

private theorem erase_degree {r : ℕ} {a : ℤ} {I : Finset (Fin r)}
    (h : (I.card : ℤ) = a) {i : Fin r} (hi : i ∈ I) :
    ((I.erase i).card : ℤ) = a - 1 := by
  have hc := Finset.card_erase_add_one hi
  omega

private theorem boundary_cell {r : ℕ} {a : ℤ} (v : Fin r → ℤ)
    (I : Finset (Fin r)) (h : (I.card : ℤ) = a) :
    boundary r a (cell r a v I) =
      ∑ i ∈ I, (-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
        (cell r (a - 1) (v + unitVector r i) (I.erase i) -
          cell r (a - 1) v (I.erase i)) := by
  simp [cell, h, boundary]

private theorem projection_cell {r : ℕ} {a : ℤ} (i : Fin r)
    (v : Fin r → ℤ) (I : Finset (Fin r)) :
    coordinateProjection r a i (cell r a v I) =
      if i ∈ I then 0 else cell r a (resetCoordinate r i v) I := by
  classical
  by_cases h : (I.card : ℤ) = a
  · simp [cell, h, coordinateProjection]
  · simp [cell, h]

private theorem translate_cell {r : ℕ} {a : ℤ} (w v : Fin r → ℤ)
    (I : Finset (Fin r)) :
    translate r a w (cell r a v I) = cell r a (v + w) I := by
  classical
  by_cases h : (I.card : ℤ) = a
  · simp [cell, h, translate]
  · simp [cell, h]

private theorem reset_apply {r : ℕ} (i j : Fin r) (v : Fin r → ℤ) :
    resetCoordinate r i v j = if j = i then 0 else v j := by
  classical
  by_cases h : j = i
  · subst j; simp [resetCoordinate, unitVector]
  · simp [resetCoordinate, unitVector, h]

private theorem reset_comm {r : ℕ} (i j : Fin r) (v : Fin r → ℤ) :
    resetCoordinate r i (resetCoordinate r j v) =
      resetCoordinate r j (resetCoordinate r i v) := by
  ext k
  simp only [reset_apply]
  split_ifs <;> rfl

private theorem reset_add_unit {r : ℕ} (i j : Fin r) (v : Fin r → ℤ) :
    resetCoordinate r i (v + unitVector r j) =
      if j = i then resetCoordinate r i v
      else resetCoordinate r i v + unitVector r j := by
  classical
  ext k
  by_cases h : j = i
  · subst j
    by_cases hk : k = i <;> simp [reset_apply, unitVector, hk]
  · by_cases hk : k = i
    · subst k
      simp [reset_apply, h, Ne.symm h, unitVector]
    · simp [reset_apply, h, hk]

private theorem boundary_nonpos (r : ℕ) (a : ℤ) (ha : a ≤ 0) :
    boundary r a = 0 := by
  apply chains_ext
  intro v I
  have hc : I.val.card = 0 := by have := I.property; omega
  have hI := Finset.card_eq_zero.mp hc
  simp [boundary, hI]

private theorem projection_boundary (r : ℕ) (i : Fin r) (a : ℤ) :
    (boundary r a).comp (coordinateProjection r a i) =
      (coordinateProjection r (a - 1) i).comp (boundary r a) := by
  classical
  apply chains_ext
  intro v I
  rw [← cell_valid v I]
  simp only [LinearMap.comp_apply, projection_cell]
  by_cases hi : i ∈ I.val
  · simp only [hi, ↓reduceIte, map_zero]
    rw [boundary_cell v I.val I.property, map_sum]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [LinearMap.map_smul, map_sub, projection_cell, projection_cell]
    by_cases hji : j = i
    · subst j
      simp [reset_add_unit]
    · have hm : i ∈ I.val.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩
      simp [hm]
  · simp only [hi, ↓reduceIte]
    rw [boundary_cell _ _ I.property, boundary_cell _ _ I.property, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : j ≠ i := by intro h; subst j; contradiction
    have hm : i ∉ I.val.erase j := by simp [hi]
    rw [LinearMap.map_smul, map_sub, projection_cell, projection_cell]
    simp [hm, reset_add_unit, hij]

private theorem projections_commute (r : ℕ) (i j : Fin r) (a : ℤ) :
    (coordinateProjection r a i).comp (coordinateProjection r a j) =
      (coordinateProjection r a j).comp (coordinateProjection r a i) := by
  classical
  apply chains_ext
  intro v I
  rw [← cell_valid v I]
  simp only [LinearMap.comp_apply, projection_cell]
  by_cases hi : i ∈ I.val <;> by_cases hj : j ∈ I.val <;>
    simp [hi, hj, projection_cell, reset_comm]

private theorem boundary_translate (r : ℕ) (w : Fin r → ℤ) (a : ℤ) :
    (boundary r a).comp (translate r a w) =
      (translate r (a - 1) w).comp (boundary r a) := by
  classical
  apply chains_ext
  intro v I
  rw [← cell_valid v I]
  simp only [LinearMap.comp_apply, translate_cell]
  rw [boundary_cell _ _ I.property, boundary_cell _ _ I.property, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [translate_cell, add_right_comm]

private theorem augmentation_translate (r : ℕ) (w : Fin r → ℤ) :
    (augmentation r).comp (translate r 0 w) = augmentation r := by
  apply chains_ext
  intro v I
  simp [translate, augmentation, cell_valid]

private theorem projection_list_cell {r : ℕ} {a : ℤ} (l : List (Fin r))
    (v : Fin r → ℤ) (I : Finset (Fin r)) :
    (l.foldr (fun i P ↦ (coordinateProjection r a i).comp P) LinearMap.id)
        (cell r a v I) =
      if ∀ i ∈ l, i ∉ I then cell r a (fun j ↦ if j ∈ l then 0 else v j) I else 0 := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, ih]
    by_cases hl : ∀ j ∈ l, j ∉ I
    · rw [if_pos hl, projection_cell]
      by_cases hi : i ∈ I
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        have hv : resetCoordinate r i (fun j ↦ if j ∈ l then 0 else v j) =
            (fun j ↦ if j ∈ i :: l then 0 else v j) := by
          ext j
          by_cases hji : j = i <;> simp [reset_apply, hji]
        have hall : ∀ j ∈ i :: l, j ∉ I := by
          intro j hj
          rcases List.mem_cons.mp hj with hji | hj
          · simpa only [hji] using hi
          · exact hl j hj
        rw [hv, if_pos hall]
    · simp [hl]

private theorem product_zero_degree (r : ℕ) :
    coordinateProduct r 0 r = (sectionMap r).comp (augmentation r) := by
  classical
  apply chains_ext
  intro v I
  have hI : I.val = ∅ := Finset.card_eq_zero.mp (by have := I.property; omega)
  rw [← cell_valid v I]
  have ht : (List.finRange r).take r = List.finRange r :=
    List.take_of_length_le (by simp)
  rw [coordinateProduct, ht, projection_list_cell]
  simp [hI, augmentation, sectionMap, cell]
  rfl

private theorem product_other_degree (r : ℕ) (a : ℤ) (ha : a ≠ 0) :
    coordinateProduct r a r = 0 := by
  classical
  apply chains_ext
  intro v I
  rw [← cell_valid v I]
  have ht : (List.finRange r).take r = List.finRange r :=
    List.take_of_length_le (by simp)
  rw [coordinateProduct, ht, projection_list_cell, LinearMap.zero_apply]
  have hI : I.val.Nonempty := Finset.card_pos.mp (by have := I.property; omega)
  obtain ⟨i, hi⟩ := hI
  have hn : ¬ (∀ j ∈ List.finRange r, j ∉ I.val) := by
    intro h
    exact h i (by simp) hi
  rw [if_neg hn]

private theorem chains_outside (r : ℕ) (a : ℤ) (ha : a < 0 ∨ (r : ℤ) < a) :
    Subsingleton (Chains r a) := by
  have hempty : IsEmpty (Directions r a) := ⟨fun I ↦ by
    have hc := I.property
    have hb := Finset.card_le_univ I.val
    simp only [Fintype.card_fin] at hb
    omega⟩
  infer_instance

private theorem augmentation_boundary (r : ℕ) :
    (augmentation r).comp (boundary r 1) = 0 := by
  classical
  apply chains_ext
  intro v I
  rcases I with ⟨I, hI⟩
  change (augmentation r) ((boundary r 1) (Finsupp.single (v, ⟨I, hI⟩) 1)) = 0
  rw [← cell_valid v ⟨I, hI⟩, boundary_cell v I hI, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hc := erase_degree hI hi
  simp [augmentation, cell, hc]

private theorem regroup (r : ℕ) (a : ℤ) :
    ∃ e : Chains r a ≃ₗ[ℤ] (Directions r a →₀ ((Fin r → ℤ) →₀ ℤ)),
      (∀ (v : Fin r → ℤ) (I : Directions r a),
        e (Finsupp.single (v, I) 1) = Finsupp.single I (Finsupp.single v 1)) ∧
      (∀ (w : Fin r → ℤ) (x : Chains r a) (I : Directions r a),
        e (translate r a w x) I = Finsupp.mapDomain (fun v ↦ v + w) (e x I)) := by
  classical
  let e : Chains r a ≃ₗ[ℤ] (Directions r a →₀ ((Fin r → ℤ) →₀ ℤ)) :=
    (Finsupp.domLCongr (Equiv.prodComm (Fin r → ℤ) (Directions r a))).trans
      (Finsupp.curryLinearEquiv ℤ)
  have he (v : Fin r → ℤ) (I : Directions r a) (n : ℤ) :
      e (Finsupp.single (v, I) n) = Finsupp.single I (Finsupp.single v n) := by
    simp [e, Finsupp.curryLinearEquiv, Finsupp.curry_single]
  refine ⟨e, fun v I ↦ he v I 1, ?_⟩
  intro w x I
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add c n x hc hn ih =>
    rcases c with ⟨v, J⟩
    simp only [map_add, Finsupp.add_apply, Finsupp.mapDomain_add, ih]
    congr 1
    by_cases hJI : J = I <;>
      simp [translate, cell_valid, he, Finsupp.smul_single, hJI]

private theorem rank_zero : ∃ e : Chains 0 0 ≃ₗ[ℤ] ℤ,
    e.toLinearMap = augmentation 0 ∧ e.symm.toLinearMap = sectionMap 0 := by
  have hs : (augmentation 0).comp (sectionMap 0) = LinearMap.id := by
    ext
    simp [sectionMap, augmentation, cell]
  have ht : (sectionMap 0).comp (augmentation 0) = LinearMap.id := by
    apply chains_ext
    intro v I
    have hv : v = 0 := Subsingleton.elim _ _
    rcases I with ⟨I, h⟩
    have hI : I = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ Fin.elim0 i)
    subst I
    simp [sectionMap, augmentation, hv, cell]
  exact ⟨LinearEquiv.ofLinearMap (augmentation 0) (sectionMap 0) hs ht, rfl, rfl⟩

private theorem signs_cancel_ordered {r : ℕ} (I : Finset (Fin r))
    {i j : Fin r} (hi : i ∈ I) (hij : i < j) :
    (-1 : ℤ) ^ (I.filter (fun k ↦ k < i)).card *
        (-1 : ℤ) ^ ((I.erase i).filter (fun k ↦ k < j)).card +
      (-1 : ℤ) ^ (I.filter (fun k ↦ k < j)).card *
        (-1 : ℤ) ^ ((I.erase j).filter (fun k ↦ k < i)).card = 0 := by
  have he : (I.erase j).filter (fun k ↦ k < i) = I.filter (fun k ↦ k < i) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp [not_lt_of_ge hij.le]
  have hc : (I.filter (fun k ↦ k < j)).card =
      ((I.erase i).filter (fun k ↦ k < j)).card + 1 := by
    rw [Finset.filter_erase]
    exact (Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hi, hij⟩)).symm
  rw [he, hc, pow_succ]
  ring

private theorem signs_cancel {r : ℕ} (I : Finset (Fin r))
    {i j : Fin r} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    (-1 : ℤ) ^ (I.filter (fun k ↦ k < i)).card *
        (-1 : ℤ) ^ ((I.erase i).filter (fun k ↦ k < j)).card +
      (-1 : ℤ) ^ (I.filter (fun k ↦ k < j)).card *
        (-1 : ℤ) ^ ((I.erase j).filter (fun k ↦ k < i)).card = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact signs_cancel_ordered I hi h
  · simpa only [add_comm] using signs_cancel_ordered I hj h

private noncomputable def doubleFace {r : ℕ} (b : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) (i j : Fin r) : Chains r b :=
  (cell r b (v + unitVector r i + unitVector r j) ((I.erase i).erase j) -
    cell r b (v + unitVector r i) ((I.erase i).erase j)) -
  (cell r b (v + unitVector r j) ((I.erase i).erase j) -
    cell r b v ((I.erase i).erase j))

private theorem doubleFace_comm {r : ℕ} (b : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) (i j : Fin r) :
    doubleFace b v I i j = doubleFace b v I j i := by
  have he : (I.erase i).erase j = (I.erase j).erase i := by
    ext k
    simp only [Finset.mem_erase]
    tauto
  simp only [doubleFace, he, add_right_comm v]
  abel

private theorem boundary_squared (r : ℕ) (a : ℤ) :
    (boundary r (a - 1)).comp (boundary r a) = 0 := by
  classical
  apply chains_ext
  intro v I
  rw [← cell_valid v I]
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [boundary_cell v I.val I.property, map_sum]
  let f : Fin r × Fin r → Chains r (a - 1 - 1) := fun p ↦
    ((-1 : ℤ) ^ (I.val.filter (fun k ↦ k < p.1)).card *
      (-1 : ℤ) ^ ((I.val.erase p.1).filter (fun k ↦ k < p.2)).card) •
        doubleFace (a - 1 - 1) v I.val p.1 p.2
  have hexp :
      ∑ i ∈ I.val, boundary r (a - 1)
          ((-1 : ℤ) ^ (I.val.filter (fun j ↦ j < i)).card •
            (cell r (a - 1) (v + unitVector r i) (I.val.erase i) -
              cell r (a - 1) v (I.val.erase i))) =
        ∑ i ∈ I.val, ∑ j ∈ I.val.erase i, f (i, j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [LinearMap.map_smul, map_sub, boundary_cell _ _ (erase_degree I.property hi),
      boundary_cell _ _ (erase_degree I.property hi), ← Finset.sum_sub_distrib,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [f, doubleFace, smul_sub, mul_smul]
  rw [hexp]
  have hsum : (∑ p ∈ I.val.offDiag, f p) =
      ∑ i ∈ I.val, ∑ j ∈ I.val.erase i, f (i, j) := by
    apply Finset.sum_finset_product
    intro p
    simp only [Finset.mem_offDiag, Finset.mem_erase]
    tauto
  rw [← hsum]
  refine Finset.sum_involution (fun p _ ↦ p.swap) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hi, hj, hij⟩ := Finset.mem_offDiag.mp hp
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [← doubleFace_comm _ v I.val p.1 p.2, ← add_smul, signs_cancel I.val hi hj hij,
      zero_smul]
  · intro p hp _ he
    have hij := (Finset.mem_offDiag.mp hp).2.2
    exact hij (congrArg Prod.snd he)
  · intro p hp
    obtain ⟨hi, hj, hij⟩ := Finset.mem_offDiag.mp hp
    exact (Finset.mem_offDiag (x := p.swap)).mpr ⟨hj, hi, hij.symm⟩
  · intro p hp
    exact Prod.swap_swap p

/-- The cubical boundary squares to zero, coordinate projections are commuting chain
maps, their full product is the origin projection, and the basis decomposes into regular
translation orbits. All integer degrees and rank zero are included.

Source: the agent-written coordinate lemma extracted from the integral lattice contraction;
Stacks Tag 0623 supplies the comparison alternating differential only.
(blueprint: lem-sfb-cubical-boundary-coordinate-projections).

Proof, following the eight steps of the DAG:
1. Use def-weil-pbc-free-module: extend each prescribed basis image by finite integer
linear combinations. Each boundary has at most twice the rank many terms. In degrees
outside the range the direction type is empty, so the group and all its maps are zero.
2. For distinct directions i < j pair the two orders of deleting i and j. The resulting
four translated faces coincide, while their sign exponents differ by one. They cancel.
For degree one the next boundary is zero, and outside the range the domain is zero.
3. An edge boundary has augmentation 1 - 1 = 0. The square-zero and augmentation equations
are precisely the augmented chain-complex conditions of
 def-weil-pbc-module-chain-complex-homology; no exactness is asserted here.
4. If i is absent from the directions, resetting i commutes termwise with every face.
If i is present, all other faces are killed and its two i-faces have the same reset.
Thus each projection commutes with the boundary, also in the zero-degree cases.
5. Two projections either kill the same cell or reset two coordinates in either order.
Successive projections kill a cell meeting the processed coordinates and otherwise reset
those coordinates. The full product sends vertices to the origin and kills all other cells.
6. Translations add vectors and commute termwise with all boundary translations, without
changing the sign or the direction subset. Augmentation remains one on every vertex.
7. Group the finitely supported coefficients by direction subset. The inverse ungroups
them, so the two maps fix all coefficients. Translation moves v to v + w in each summand.
Each summand has one free orbit, since translation sends the origin to w, uniquely.
8. At rank zero there is one lattice vector and one empty direction set. Augmentation and
the origin section identify its free group with the integers. Every other term vanishes;
the empty product is the identity, including the identity of a zero group. -/
theorem boundary_coordinate_projections (r : ℕ) :
    (∀ a : ℤ, Module.Free ℤ (Chains r a)) ∧
    (∀ a : ℤ, a < 0 ∨ (r : ℤ) < a → Subsingleton (Chains r a)) ∧
    (∀ a : ℤ, a ≤ 0 → boundary r a = 0) ∧
    (∀ a : ℤ, (boundary r (a - 1)).comp (boundary r a) = 0) ∧
    (augmentation r).comp (boundary r 1) = 0 ∧
    (∀ (i : Fin r) (a : ℤ),
      (boundary r a).comp (coordinateProjection r a i) =
        (coordinateProjection r (a - 1) i).comp (boundary r a)) ∧
    (∀ (i j : Fin r) (a : ℤ),
      (coordinateProjection r a i).comp (coordinateProjection r a j) =
        (coordinateProjection r a j).comp (coordinateProjection r a i)) ∧
    coordinateProduct r 0 r = (sectionMap r).comp (augmentation r) ∧
    (∀ a : ℤ, a ≠ 0 → coordinateProduct r a r = 0) ∧
    (∀ (w : Fin r → ℤ) (a : ℤ),
      (boundary r a).comp (translate r a w) =
        (translate r (a - 1) w).comp (boundary r a)) ∧
    (∀ w : Fin r → ℤ, (augmentation r).comp (translate r 0 w) = augmentation r) ∧
    (∀ a : ℤ, Finite (Directions r a)) ∧
    (∀ a : ℤ, ∃ e : Chains r a ≃ₗ[ℤ] (Directions r a →₀ ((Fin r → ℤ) →₀ ℤ)),
      (∀ (v : Fin r → ℤ) (I : Directions r a),
        e (Finsupp.single (v, I) 1) = Finsupp.single I (Finsupp.single v 1)) ∧
      (∀ (w : Fin r → ℤ) (x : Chains r a) (I : Directions r a),
        e (translate r a w x) I = Finsupp.mapDomain (fun v ↦ v + w) (e x I))) ∧
    (r = 0 → ∃ e : Chains r 0 ≃ₗ[ℤ] ℤ,
      e.toLinearMap = augmentation r ∧ e.symm.toLinearMap = sectionMap r) := by
  refine ⟨fun a ↦ inferInstance, chains_outside r, boundary_nonpos r, boundary_squared r,
    augmentation_boundary r, projection_boundary r, projections_commute r,
    product_zero_degree r, product_other_degree r, boundary_translate r,
    augmentation_translate r, ?_, regroup r, ?_⟩
  · intro a
    change Finite {I : Finset (Fin r) // (I.card : ℤ) = a}
    infer_instance
  · intro hr
    subst r
    exact rank_zero

end IntegralLatticeCubical
