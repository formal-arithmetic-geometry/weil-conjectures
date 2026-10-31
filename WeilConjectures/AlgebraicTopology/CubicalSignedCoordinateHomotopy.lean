/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.AlgebraicTopology.IntegralLatticeCubicalDefs
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! # Signed coordinate homotopies on integral cubical chains

Source: the agent-written signed-path calculation in the DAG, steps 1--7
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy). Stacks Project, more-algebra.tex,
Tag 0623, preceding alternating differential, is comparison only. The blueprint route
location is the direct-images proof, paragraph (3), in the six-functors-basics chapter.

The existing cubical cells and boundary are reused. All new maps have explicit data;
only the identities are postponed. No translation equivariance is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IntegralLatticeCubical

/-- The finite oriented sum from zero to `n`, with the negative orientation for `n < 0`.
Source: the displayed three-case definition of `Sigma` in the agent-written DAG lemma
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy). -/
def signedCoordinateSum {A : Type u} [AddCommGroup A] (n : ℤ) (b : ℤ → A) : A :=
  if 0 < n then ∑ k ∈ Finset.Ico 0 n, b k
  else if n = 0 then 0 else -∑ k ∈ Finset.Ico n 0, b k

/-- Reset the `i`th coordinate: `rho_i(v) = v - v_i u_i`.
Source: the coordinate projection in the agent-written DAG lemma
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy). Named apart from the sibling
lem-sfb-cubical-boundary-coordinate-projections `resetCoordinate`, which has the same body. -/
def pathResetCoordinate (r : ℕ) (i : Fin r) (v : Fin r → ℤ) : Fin r → ℤ :=
  v - v i • unitVector r i

/-- Kill cells containing `i`, and reset coordinate `i` on the other cells, extended
by their unique finite integral expansion. Source: the displayed formula for `p_i`
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy). Named apart from the sibling
`coordinateProjection r a i` of lem-sfb-cubical-boundary-coordinate-projections, which has
the same body with the degree before the coordinate. -/
noncomputable def pathCoordinateProjection (r : ℕ) (i : Fin r) (a : ℤ) :
    Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun c ↦
    if i ∈ c.2.val then 0 else cell r a (pathResetCoordinate r i c.1) c.2.val

/-- Insert coordinate `i` with its alternating sign, summing the oriented finite path
from zero to `v_i`; kill cells already containing `i`. The linear combination is the
actual homomorphism extension, and the empty cell index makes it zero out of range.
Source: the displayed formula for `H_i` and proof step 3 of the agent-written DAG lemma
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy). -/
noncomputable def coordinateHomotopy (r : ℕ) (i : Fin r) (a : ℤ) :
    Chains r a →ₗ[ℤ] Chains r (a + 1) :=
  Finsupp.linearCombination ℤ fun c ↦
    if i ∈ c.2.val then 0 else
      (-1 : ℤ) ^ (c.2.val.filter (fun j ↦ j < i)).card •
        signedCoordinateSum (c.1 i) (fun k ↦
          cell r (a + 1) (pathResetCoordinate r i c.1 + k • unitVector r i)
            (insert i c.2.val))

private theorem signed_sum_step {A : Type*} [AddCommGroup A] (b : ℤ → A) (n : ℤ) :
    signedCoordinateSum (n + 1) b - signedCoordinateSum n b = b n := by
  classical
  by_cases h : 0 ≤ n
  · have he : Finset.Ico (0 : ℤ) (n + 1) = insert n (Finset.Ico 0 n) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    by_cases hz : n = 0
    · subst n
      have he' : Finset.Ico (0 : ℤ) 1 = {0} := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      simp [signedCoordinateSum, he']
    · simp [signedCoordinateSum, show 0 < n by omega, show 0 < n + 1 by omega,
        he, Finset.sum_insert]
  · have he : Finset.Ico n (0 : ℤ) = insert n (Finset.Ico (n + 1) 0) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    by_cases hz : n + 1 = 0
    · have hn : n = -1 := by omega
      subst n
      simp [signedCoordinateSum, he]
    · simp [signedCoordinateSum, show ¬ 0 < n by omega,
        show ¬ 0 < n + 1 by omega, show n ≠ 0 by omega, hz, he, Finset.sum_insert]

private theorem signed_sum_telescope {A : Type*} [AddCommGroup A] (b : ℤ → A) (n : ℤ) :
    signedCoordinateSum n (fun k ↦ b (k + 1) - b k) = b n - b 0 := by
  induction n using Int.induction_on with
  | zero => simp [signedCoordinateSum]
  | succ n ih =>
    have h := signed_sum_step (fun k ↦ b (k + 1) - b k) n
    rw [ih] at h
    exact (sub_eq_iff_eq_add.mp h).trans (by abel)
  | pred n ih =>
    have h := signed_sum_step (fun k ↦ b (k + 1) - b k) (- (n : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    calc
      _ = (b (- (n : ℤ)) - b 0) - (b (- (n : ℤ)) - b (- (n : ℤ) - 1)) :=
        eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)
      _ = _ := by abel

private theorem signed_sum_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (b : ℤ → A) (n : ℤ) :
    f (signedCoordinateSum n b) = signedCoordinateSum n (fun k ↦ f (b k)) := by
  classical
  unfold signedCoordinateSum
  split_ifs <;> simp only [map_sum, map_zero, map_neg]

private theorem cell_single (r : ℕ) (a : ℤ) (v : Fin r → ℤ) (I : Directions r a) :
    cell r a v I.val = Finsupp.single (v, I) 1 := by
  simp [cell, I.property]

private theorem cast_cell (r : ℕ) (a b : ℤ) (h : a = b)
    (v : Fin r → ℤ) (I : Finset (Fin r)) :
    LinearEquiv.cast (R := ℤ) (M := Chains r) h (cell r a v I) = cell r b v I := by
  subst b
  rfl

private theorem boundary_cell (r : ℕ) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) (h : (I.card : ℤ) = a) :
    boundary r a (cell r a v I) =
      ∑ j ∈ I, (-1 : ℤ) ^ (I.filter (fun k ↦ k < j)).card •
        (cell r (a - 1) (v + unitVector r j) (I.erase j) -
          cell r (a - 1) v (I.erase j)) := by
  classical
  simp [cell, h, boundary]

private theorem projection_cell (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) :
    pathCoordinateProjection r i a (cell r a v I.val) =
      if i ∈ I.val then 0 else cell r a (pathResetCoordinate r i v) I.val := by
  classical
  rw [cell_single]
  simp [pathCoordinateProjection]

private theorem homotopy_cell (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Finset (Fin r)) (h : (I.card : ℤ) = a) :
    coordinateHomotopy r i a (cell r a v I) =
      if i ∈ I then 0 else
        (-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
          signedCoordinateSum (v i) (fun k ↦
            cell r (a + 1) (pathResetCoordinate r i v + k • unitVector r i) (insert i I)) := by
  classical
  simp [cell, h, coordinateHomotopy]

private theorem directions_range (r : ℕ) (a : ℤ) (I : Directions r a) :
    0 ≤ a ∧ a ≤ r := by
  have hc := Finset.card_le_univ I.val
  have hp := I.property
  simp only [Fintype.card_fin] at hc
  omega

private theorem boundary_nonpositive (r : ℕ) (a : ℤ) (h : a ≤ 0) : boundary r a = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro c z
  obtain ⟨v, I⟩ := c
  have he : I.val = ∅ := by
    apply Finset.card_eq_zero.mp
    have := I.property
    omega
  simp [boundary, he]

private theorem projection_outside (r : ℕ) (i : Fin r) (a : ℤ)
    (h : a < 0 ∨ (r : ℤ) < a) : pathCoordinateProjection r i a = 0 := by
  apply Finsupp.lhom_ext
  intro c z
  have := directions_range r a c.2
  omega

private theorem homotopy_top_outside (r : ℕ) (i : Fin r) (a : ℤ)
    (h : a = (r : ℤ) ∨ a < 0 ∨ (r : ℤ) < a) : coordinateHomotopy r i a = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro c z
  have hr := directions_range r a c.2
  have ht : a = (r : ℤ) := by omega
  have hc : c.2.val.card = r := by have := c.2.property; omega
  have he : c.2.val = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hc)
  simp [coordinateHomotopy, he]

private noncomputable def pathSum (r : ℕ) (i : Fin r) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) : Chains r a :=
  signedCoordinateSum (v i) (fun k ↦
    cell r a (pathResetCoordinate r i v + k • unitVector r i) I)

private theorem reset_self (r : ℕ) (i : Fin r) (v : Fin r → ℤ) :
    pathResetCoordinate r i v + v i • unitVector r i = v := by
  simp [pathResetCoordinate]

private theorem reset_shift (r : ℕ) (i : Fin r) (v : Fin r → ℤ) :
    pathResetCoordinate r i (v + unitVector r i) = pathResetCoordinate r i v := by
  simp only [pathResetCoordinate, Pi.add_apply, unitVector, Pi.single_eq_same]
  simp only [add_smul, one_smul]
  abel

private theorem reset_other (r : ℕ) (i j : Fin r) (h : j ≠ i) (v : Fin r → ℤ) :
    pathResetCoordinate r i (v + unitVector r j) =
      pathResetCoordinate r i v + unitVector r j := by
  simp only [pathResetCoordinate, Pi.add_apply, unitVector, Pi.single_eq_of_ne h.symm,
    add_zero]
  abel

private theorem pathSum_step (r : ℕ) (i : Fin r) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) :
    pathSum r i a (v + unitVector r i) I - pathSum r i a v I = cell r a v I := by
  unfold pathSum
  rw [reset_shift]
  simp only [Pi.add_apply, unitVector, Pi.single_eq_same]
  rw [signed_sum_step]
  exact congrArg (fun w ↦ cell r a w I) (reset_self r i v)

private theorem pathSum_telescope (r : ℕ) (i : Fin r) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) :
    signedCoordinateSum (v i) (fun k ↦
      cell r a (pathResetCoordinate r i v + k • unitVector r i + unitVector r i) I -
        cell r a (pathResetCoordinate r i v + k • unitVector r i) I) =
      cell r a v I - cell r a (pathResetCoordinate r i v) I := by
  have he (k : ℤ) : pathResetCoordinate r i v + k • unitVector r i + unitVector r i =
      pathResetCoordinate r i v + (k + 1) • unitVector r i := by
    simp [add_smul, add_assoc]
  simp_rw [he]
  rw [signed_sum_telescope (fun k ↦
    cell r a (pathResetCoordinate r i v + k • unitVector r i) I)]
  rw [zero_smul, add_zero, reset_self]

private theorem signed_sum_sub {A : Type*} [AddCommGroup A] (b c : ℤ → A) (n : ℤ) :
    signedCoordinateSum n (fun k ↦ b k - c k) =
      signedCoordinateSum n b - signedCoordinateSum n c := by
  classical
  unfold signedCoordinateSum
  split_ifs <;> simp [Finset.sum_sub_distrib]
  abel

private theorem signed_sum_smul {A : Type*} [AddCommGroup A] (z : ℤ)
    (b : ℤ → A) (n : ℤ) :
    signedCoordinateSum n (fun k ↦ z • b k) = z • signedCoordinateSum n b :=
  (signed_sum_map (z • AddMonoidHom.id A) b n).symm

private theorem signed_sum_finset {A X : Type*} [AddCommGroup A]
    (s : Finset X) (b : X → ℤ → A) (n : ℤ) :
    signedCoordinateSum n (fun k ↦ ∑ j ∈ s, b j k) =
      ∑ j ∈ s, signedCoordinateSum n (b j) := by
  classical
  unfold signedCoordinateSum
  split_ifs
  · exact Finset.sum_comm
  · simp
  · rw [Finset.sum_comm, Finset.sum_neg_distrib]

private theorem cast_pathSum (r : ℕ) (i : Fin r) (a b : ℤ) (h : a = b)
    (v : Fin r → ℤ) (I : Finset (Fin r)) :
    LinearEquiv.cast (R := ℤ) (M := Chains r) h (pathSum r i a v I) =
      pathSum r i b v I := by
  subst b
  rfl

private theorem lower_homotopy_cell (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Finset (Fin r)) (h : (I.card : ℤ) = a - 1) :
    LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
      (coordinateHomotopy r i (a - 1) (cell r (a - 1) v I)) =
      if i ∈ I then 0 else (-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
        pathSum r i a v (insert i I) := by
  classical
  rw [homotopy_cell r i (a - 1) v I h]
  split_ifs
  · exact map_zero _
  · rw [map_smul]
    change _ • (LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1))
      (pathSum r i (a - 1 + 1) v (insert i I)) = _
    rw [cast_pathSum]

private theorem incoming_cell (r : ℕ) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) (h : (I.card : ℤ) = a + 1) :
    incomingBoundary r a (cell r (a + 1) v I) =
      ∑ j ∈ I, (-1 : ℤ) ^ (I.filter (fun k ↦ k < j)).card •
        (cell r a (v + unitVector r j) (I.erase j) - cell r a v (I.erase j)) := by
  classical
  simp only [incomingBoundary, LinearMap.comp_apply, boundary_cell r (a + 1) v I h,
    LinearEquiv.coe_toLinearMap, map_sum, map_smul, map_sub, cast_cell]

private theorem sign_square (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← mul_pow]
  simp

private theorem filter_insert_self (r : ℕ) (i : Fin r) (I : Finset (Fin r)) :
    (insert i I).filter (fun j ↦ j < i) = I.filter (fun j ↦ j < i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨h | h, hj⟩
    · subst j; exact (lt_irrefl _ hj).elim
    · exact ⟨h, hj⟩
  · intro h; exact ⟨Or.inr h.1, h.2⟩

private theorem filter_erase_self (r : ℕ) (i : Fin r) (I : Finset (Fin r)) :
    (I.erase i).filter (fun j ↦ j < i) = I.filter (fun j ↦ j < i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun h ↦ ⟨h.1.2, h.2⟩
  · exact fun h ↦ ⟨⟨ne_of_lt h.2, h.1⟩, h.2⟩

private theorem face_sign_cancel (r : ℕ) (i j : Fin r) (I : Finset (Fin r))
    (hi : i ∉ I) (hj : j ∈ I) :
    (-1 : ℤ) ^ (I.filter (fun k ↦ k < i)).card *
        (-1 : ℤ) ^ ((insert i I).filter (fun k ↦ k < j)).card =
      -((-1 : ℤ) ^ (I.filter (fun k ↦ k < j)).card *
        (-1 : ℤ) ^ ((I.erase j).filter (fun k ↦ k < i)).card) := by
  classical
  have hne : j ≠ i := by intro h; subst j; exact hi hj
  have he : (I.filter (fun k ↦ k < i)).card +
        ((insert i I).filter (fun k ↦ k < j)).card =
      (I.filter (fun k ↦ k < j)).card +
        ((I.erase j).filter (fun k ↦ k < i)).card + 1 := by
    by_cases hij : i < j
    · have hji : ¬ j < i := not_lt_of_ge (le_of_lt hij)
      have hni : i ∉ I.filter (fun k ↦ k < j) := by simp [hi]
      have hnj : j ∉ I.filter (fun k ↦ k < i) := by simp [hji]
      simp only [Finset.filter_insert, if_pos hij, Finset.card_insert_of_notMem hni,
        Finset.filter_erase, Finset.erase_eq_of_notMem hnj]
      omega
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) hne
      have hm : j ∈ I.filter (fun k ↦ k < i) := by simp [hj, hji]
      have hc := Finset.card_erase_add_one hm
      simp only [Finset.filter_insert, if_neg hij, Finset.filter_erase]
      omega
  rw [← pow_add, ← pow_add, he, pow_succ]
  ring

private noncomputable def facePath (r : ℕ) (i : Fin r) (a : ℤ) (v : Fin r → ℤ)
    (I : Finset (Fin r)) (j : Fin r) : Chains r a :=
  signedCoordinateSum (v i) (fun k ↦
    cell r a (pathResetCoordinate r i v + k • unitVector r i + unitVector r j) I -
      cell r a (pathResetCoordinate r i v + k • unitVector r i) I)

private theorem facePath_other (r : ℕ) (i j : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Finset (Fin r)) (hji : j ≠ i) :
    facePath r i a v I j = pathSum r i a (v + unitVector r j) I -
      pathSum r i a v I := by
  unfold facePath pathSum
  rw [signed_sum_sub, reset_other r i j hji]
  have hz : (v + unitVector r j) i = v i := by
    simp [unitVector, Pi.single_eq_of_ne hji.symm]
  rw [hz]
  congr 2
  funext k
  congr 1
  abel

private theorem signed_sum_linear {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →ₗ[ℤ] B) (b : ℤ → A) (n : ℤ) :
    f (signedCoordinateSum n b) = signedCoordinateSum n (fun k ↦ f (b k)) := by
  classical
  unfold signedCoordinateSum
  split_ifs <;> simp only [map_sum, map_zero, map_neg]

private theorem upper_absent (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) (hi : i ∉ I.val) :
    incomingBoundary r a (coordinateHomotopy r i a (cell r a v I.val)) =
      ∑ j ∈ insert i I.val,
        ((-1 : ℤ) ^ (I.val.filter (fun k ↦ k < i)).card *
          (-1 : ℤ) ^ ((insert i I.val).filter (fun k ↦ k < j)).card) •
          facePath r i a v ((insert i I.val).erase j) j := by
  classical
  have hc : ((insert i I.val).card : ℤ) = a + 1 := by
    rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, I.property]
  rw [homotopy_cell r i a v I.val I.property, if_neg hi, map_smul,
    signed_sum_linear (incomingBoundary r a)]
  simp_rw [incoming_cell r a _ _ hc]
  rw [signed_sum_finset, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [signed_sum_smul, smul_smul]
  rfl

private theorem lower_expansion (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) :
    LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
      (coordinateHomotopy r i (a - 1) (boundary r a (cell r a v I.val))) =
      ∑ j ∈ I.val, (-1 : ℤ) ^ (I.val.filter (fun k ↦ k < j)).card •
        (if i ∈ I.val.erase j then 0 else
          (-1 : ℤ) ^ ((I.val.erase j).filter (fun k ↦ k < i)).card •
            (pathSum r i a (v + unitVector r j) (insert i (I.val.erase j)) -
              pathSum r i a v (insert i (I.val.erase j)))) := by
  classical
  rw [boundary_cell r a v I.val I.property]
  simp only [map_sum, map_smul, map_sub]
  apply Finset.sum_congr rfl
  intro j hj
  have hc : ((I.val.erase j).card : ℤ) = a - 1 := by
    have := Finset.card_erase_add_one hj
    have := I.property
    omega
  rw [lower_homotopy_cell r i a _ _ hc, lower_homotopy_cell r i a _ _ hc]
  split_ifs <;> simp only [sub_self, smul_sub]

private theorem homotopy_present (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) (hi : i ∈ I.val) :
    incomingBoundary r a (coordinateHomotopy r i a (cell r a v I.val)) +
      LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
        (coordinateHomotopy r i (a - 1) (boundary r a (cell r a v I.val))) =
      cell r a v I.val := by
  classical
  rw [homotopy_cell r i a v I.val I.property, if_pos hi, map_zero, zero_add,
    lower_expansion]
  rw [Finset.sum_eq_single i]
  · simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, if_false,
      Finset.insert_erase hi, filter_erase_self, pathSum_step, smul_smul, sign_square,
      one_smul]
  · intro j hj hji
    have hm : i ∈ I.val.erase j := Finset.mem_erase.mpr ⟨hji.symm, hi⟩
    simp [hm]
  · exact fun h ↦ (h hi).elim

private theorem homotopy_absent (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) (hi : i ∉ I.val) :
    incomingBoundary r a (coordinateHomotopy r i a (cell r a v I.val)) +
      LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
        (coordinateHomotopy r i (a - 1) (boundary r a (cell r a v I.val))) =
      cell r a v I.val - cell r a (pathResetCoordinate r i v) I.val := by
  classical
  rw [upper_absent r i a v I hi, lower_expansion, Finset.sum_insert hi]
  have hmain :
      ((-1 : ℤ) ^ (I.val.filter (fun k ↦ k < i)).card *
        (-1 : ℤ) ^ ((insert i I.val).filter (fun k ↦ k < i)).card) •
        facePath r i a v ((insert i I.val).erase i) i =
      cell r a v I.val - cell r a (pathResetCoordinate r i v) I.val := by
    rw [filter_insert_self, sign_square, one_smul, Finset.erase_insert hi]
    exact pathSum_telescope r i a v I.val
  rw [hmain, add_assoc]
  suffices hh :
      (∑ j ∈ I.val,
        ((-1 : ℤ) ^ (I.val.filter (fun k ↦ k < i)).card *
          (-1 : ℤ) ^ ((insert i I.val).filter (fun k ↦ k < j)).card) •
          facePath r i a v ((insert i I.val).erase j) j) +
      (∑ j ∈ I.val, (-1 : ℤ) ^ (I.val.filter (fun k ↦ k < j)).card •
        (if i ∈ I.val.erase j then 0 else
          (-1 : ℤ) ^ ((I.val.erase j).filter (fun k ↦ k < i)).card •
            (pathSum r i a (v + unitVector r j) (insert i (I.val.erase j)) -
              pathSum r i a v (insert i (I.val.erase j))))) = 0 by
    rw [hh, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  have hm : i ∉ I.val.erase j := fun h ↦ hi (Finset.mem_of_mem_erase h)
  rw [if_neg hm, smul_smul, face_sign_cancel r i j I.val hi hj,
    Finset.erase_insert_of_ne hji.symm, facePath_other r i j a v _ hji, neg_smul,
    neg_add_cancel]

private theorem homotopy_basis (r : ℕ) (i : Fin r) (a : ℤ)
    (v : Fin r → ℤ) (I : Directions r a) :
    incomingBoundary r a (coordinateHomotopy r i a (cell r a v I.val)) +
      LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
        (coordinateHomotopy r i (a - 1) (boundary r a (cell r a v I.val))) =
      if i ∈ I.val then cell r a v I.val else
        cell r a v I.val - cell r a (pathResetCoordinate r i v) I.val := by
  classical
  by_cases hi : i ∈ I.val
  · rw [if_pos hi]
    exact homotopy_present r i a v I hi
  · rw [if_neg hi]
    exact homotopy_absent r i a v I hi

private theorem homotopy_map (r : ℕ) (i : Fin r) (a : ℤ) :
    (incomingBoundary r a).comp (coordinateHomotopy r i a) +
      ((LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)).toLinearMap.comp
        (coordinateHomotopy r i (a - 1))).comp (boundary r a) =
      LinearMap.id - pathCoordinateProjection r i a := by
  classical
  apply Finsupp.lhom_ext
  rintro ⟨v, I⟩ z
  have hz : Finsupp.single (v, I) z = z • cell r a v I.val := by
    rw [cell_single]
    simp
  rw [hz]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.sub_apply, LinearMap.id_apply, projection_cell, homotopy_basis]
  split_ifs <;> simp

/-- The signed-sum identities and the cubical coordinate homotopy identity, including
its two basis cases and the zero extensions in every integer degree.

Source: the seven-step agent-written proof of the DAG lemma; Stacks Tag 0623's preceding
alternating differential is comparison only
(blueprint: lem-sfb-cubical-signed-coordinate-homotopy).

Proof plan:
1. For `n > 0`, adjoining the last summand gives the recurrence. For `n = 0` it is
`b(0) - 0 = b(0)`. For `n <= -2`, subtract the two negatively oriented sums; only
`b(n)` remains. At `n = -1` the difference is `0 - (-b(-1))`.
2. Telescope successive differences. The positive interval leaves `b(n) - b(0)`;
the negative interval leaves `b(0) - b(n)` before negation. At zero both sides vanish.
Finite distributivity and additivity of homomorphisms commute with these signed sums.
3. If `i` is absent, inserting it increases the cardinality by one. Extend the displayed
finite sum using the unique basis expansion of def-weil-pbc-free-module, implemented by
`Finsupp.linearCombination`. If `i` is present the value is zero. In top degree every
subset contains `i`; outside the rank range there are no basis vectors. The same
extension gives the boundary and projection, with boundary zero in nonpositive degrees.
4. For `i` absent, the boundary face deleting the inserted `i` has the product of two
equal signs, hence coefficient one. Its signed sum telescopes to the cell minus its reset.
5. For each other direction `j`, the exponents in boundary-after-homotopy and
homotopy-after-boundary differ by one: for `i < j` they are `q_i + q_j + 1` and
`q_i + q_j`; for `j < i` they are `q_i + q_j` and `q_i + q_j - 1`.
The underlying signed paths coincide because resetting `i` commutes with translation
in `j`. Thus these terms cancel, including negative paths. An empty direction set
has no such faces and its degree-zero outgoing boundary is zero.
6. For `i` present, homotopy is zero. All boundary faces except the `i` face still
contain `i` and are killed by homotopy. The remaining two signs multiply to one;
the path sums at `v_i + 1` and `v_i` differ by the original cell. This works in top
degree, at `v_i = -1` (zero minus the negative cell) and at zero (the cell minus zero).
7. The two cases give the map identity by the unique finite basis expansion. Outside
the rank range the source is zero, including degrees `-1` and `r + 1`. At degree zero
the composite through degree `-1` vanishes. For `r = 0` there is no `i : Fin r`, so
all coordinate assertions are vacuous while the signed-sum identities remain valid.
-/
theorem signedCoordinateHomotopy (r : ℕ) :
    (∀ (A : Type u) (_ : AddCommGroup A) (b : ℤ → A) (n : ℤ),
      signedCoordinateSum n (fun k ↦ b (k + 1) - b k) = b n - b 0 ∧
      signedCoordinateSum (n + 1) b - signedCoordinateSum n b = b n) ∧
    (∀ a : ℤ, a ≤ 0 → boundary r a = 0) ∧
    (∀ (i : Fin r) (a : ℤ),
      a < 0 ∨ (r : ℤ) < a → pathCoordinateProjection r i a = 0) ∧
    (∀ (i : Fin r) (a : ℤ),
      a = (r : ℤ) ∨ a < 0 ∨ (r : ℤ) < a → coordinateHomotopy r i a = 0) ∧
    (∀ (i : Fin r) (a : ℤ) (v : Fin r → ℤ) (I : Directions r a),
      pathCoordinateProjection r i a (cell r a v I.val) =
        if i ∈ I.val then 0 else cell r a (pathResetCoordinate r i v) I.val) ∧
    (∀ (i : Fin r) (a : ℤ) (v : Fin r → ℤ) (I : Directions r a),
      coordinateHomotopy r i a (cell r a v I.val) =
        if i ∈ I.val then 0 else
          (-1 : ℤ) ^ (I.val.filter (fun j ↦ j < i)).card •
            signedCoordinateSum (v i) (fun k ↦
              cell r (a + 1) (pathResetCoordinate r i v + k • unitVector r i)
                (insert i I.val))) ∧
    (∀ (i : Fin r) (a : ℤ),
      (incomingBoundary r a).comp (coordinateHomotopy r i a) +
        ((LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)).toLinearMap.comp
          (coordinateHomotopy r i (a - 1))).comp (boundary r a) =
        LinearMap.id - pathCoordinateProjection r i a) ∧
    (∀ (i : Fin r) (a : ℤ) (v : Fin r → ℤ) (I : Directions r a),
      incomingBoundary r a (coordinateHomotopy r i a (cell r a v I.val)) +
        LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
          (coordinateHomotopy r i (a - 1) (boundary r a (cell r a v I.val))) =
        if i ∈ I.val then cell r a v I.val
        else cell r a v I.val - cell r a (pathResetCoordinate r i v) I.val) := by
  refine ⟨?_, boundary_nonpositive r, projection_outside r, homotopy_top_outside r,
    projection_cell r, ?_, homotopy_map r, homotopy_basis r⟩
  · intro A _ b n
    exact ⟨signed_sum_telescope b n, signed_sum_step b n⟩
  · intro i a v I
    exact homotopy_cell r i a v I.val I.property

end IntegralLatticeCubical
