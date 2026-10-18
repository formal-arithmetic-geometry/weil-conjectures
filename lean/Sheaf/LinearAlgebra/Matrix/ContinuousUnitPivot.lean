/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!
# Continuous elimination of a unit pivot

Source: the auxiliary elementary calculation in the DAG node
`lem-sfb-unit-pivot-schur-formula`, motivated by Hemo--Richarz--Scholbach,
*Constructible sheaves on schemes*, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula).
The paper supplies the continuous-division context; the matrix calculation is agent-written.

The five constructions below are the prescribed factors and residual block of this one node.
Index `0` is the first index; sizes `n + 1` and `m + 1` cover all positive sizes.
`Ring.inverse` agrees with inversion of units, without assuming global continuity of inversion.
-/

@[expose] public section

universe u v

namespace Matrix

/-- The diagonal factor `L₀ = diag(a⁻¹, 1, …, 1)` in the auxiliary pivot calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotScaling {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  diagonal (fun i => if i = 0 then Ring.inverse (K 0 0) else 1)

/-- The factor `L₁`, equal to the identity except for `-a⁻¹ Kᵢ₁` below the pivot,
in the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotLeftElimination {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  of (fun i j => if i ≠ 0 ∧ j = 0 then -(Ring.inverse (K 0 0) * K i 0)
    else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j)

/-- The prescribed left factor `L = L₀ L₁`, in this order, in the auxiliary calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotLeft {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  unitPivotScaling K * unitPivotLeftElimination K

/-- The factor `R₀`, equal to the identity except for `-a⁻¹ K₁ⱼ` to the right of the pivot,
in the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotRightElimination {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  of (fun i j => if i = 0 ∧ j ≠ 0 then -(Ring.inverse (K 0 0) * K 0 j)
    else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) A) i j)

/-- The reduced block `Hᵢⱼ = Kᵢⱼ - a⁻¹ Kᵢ₁ K₁ⱼ` in the auxiliary pivot calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19. Successor indices omit the first row
and column (blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotSchurComplement {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin n) (Fin m) A :=
  of (fun i j => K i.succ j.succ - Ring.inverse (K 0 0) * K i.succ 0 * K 0 j.succ)

/-- Explicit continuous unit-pivot elimination over a commutative topological ring.
Source: the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula).

The pointwise `IsUnit` clauses say that the prescribed matrices belong to the general linear
groups, whose elements are exactly the units of square matrix rings. The next four clauses
assert entrywise continuity of the two matrices and their actual inverses. The last two give
continuity of the reduced block and the prescribed block identity.

Proof plan (agent-written auxiliary calculation, not a formula stated in HRS):
1. Put `b = a⁻¹`, `N = L₁ - I`, and `P = R₀ - I`. Only the first column of `N` and the first
   row of `P` can be nonzero, with zero pivot entries. Thus `N² = P² = 0`, so their inverses
   are `I - N` and `I - P`. Matrices and finite-sum multiplication use def-weil-matrix.
2. `D = diag(a, 1, …, 1)` inverts `L₀`, so `(I - N) D` inverts `L = L₀ L₁`.
   Its pivot entry is `a`, entries below it are `Kᵢ₁`, and the other entries are those of `I`.
3. Column elimination gives `(K R₀)ᵢ₁ = Kᵢ₁` and, for `j > 1`,
   `(K R₀)ᵢⱼ = Kᵢⱼ - b Kᵢ₁ K₁ⱼ`. The latter is zero in the first row and is `H` below it.
4. Multiplication by `L₁` kills the first column below the pivot; multiplication by `L₀`
   changes the pivot from `a` to `1`, leaving `H` unchanged. This is the displayed identity.
5. Every entry of the factors, their inverses and `H` is a constant, a given continuous
   entry, or a sum/product/negative of these and the separately continuous `b`.
   Topological-ring operations therefore prove all five entrywise continuity assertions.
6. Empty reduced row/column sets give the one-row/one-column cases; if both are empty the
   identity is `b a = 1`. Empty `T` gives vacuous pointwise statements and continuous maps.
-/
theorem continuous_unitPivot_schur_formula {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {T : Type v} [TopologicalSpace T]
    {n m : ℕ} (K : T → Matrix (Fin (n + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, Continuous (fun t => K t i j))
    (hunit : ∀ t, IsUnit (K t 0 0))
    (hinv : Continuous (fun t => Ring.inverse (K t 0 0))) :
    (∀ t, IsUnit (unitPivotLeft (K t))) ∧
    (∀ t, IsUnit (unitPivotRightElimination (K t))) ∧
    (∀ i j, Continuous (fun t => unitPivotLeft (K t) i j)) ∧
    (∀ i j, Continuous (fun t => unitPivotRightElimination (K t) i j)) ∧
    (∀ i j, Continuous (fun t => Ring.inverse (unitPivotLeft (K t)) i j)) ∧
    (∀ i j, Continuous (fun t => Ring.inverse (unitPivotRightElimination (K t)) i j)) ∧
    (∀ i j, Continuous (fun t => unitPivotSchurComplement (K t) i j)) ∧
    (∀ t, unitPivotLeft (K t) * K t * unitPivotRightElimination (K t) =
      of (Fin.cases (Fin.cases 1 (fun _ => 0))
        (fun i => Fin.cases 0 (unitPivotSchurComplement (K t) i)))) := by
  classical
  -- A lower triangular matrix with identity as its reduced diagonal block.
  let lo {s : ℕ} (d : A) (c : Fin s → A) : Matrix (Fin (s + 1)) (Fin (s + 1)) A :=
    of (Fin.cases (Fin.cases d (fun _ => 0))
      (fun i => Fin.cases (c i) (fun j => (1 : Matrix (Fin s) (Fin s) A) i j)))
  have lo_mul {s : ℕ} (d e : A) (c f : Fin s → A) :
      lo d c * lo e f = lo (d * e) (fun i => c i * e + f i) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [lo, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have lo_one {s : ℕ} : lo 1 (fun _ : Fin s => 0) = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [lo, Matrix.one_apply, eq_comm]
  have hL (M : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : unitPivotLeft M = lo (Ring.inverse (M 0 0))
      (fun i => -(Ring.inverse (M 0 0) * M i.succ 0)) := by
    ext i j
    simp only [unitPivotLeft, unitPivotScaling, Matrix.diagonal_mul]
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [lo, unitPivotLeftElimination, Matrix.one_apply, eq_comm]
  have hR (M : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : unitPivotRightElimination M =
      (lo 1 (fun j => -(Ring.inverse (M 0 0) * M 0 j.succ)))ᵀ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [lo, unitPivotRightElimination, Matrix.one_apply, eq_comm]
  -- Compute the inverse factors and the elimination identity entrywise.
  have hp (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) (h : IsUnit (K 0 0)) :
      (unitPivotLeft K * lo (K 0 0) (fun i => K i.succ 0) = 1) ∧
      (unitPivotRightElimination K *
        (lo 1 (fun j => Ring.inverse (K 0 0) * K 0 j.succ))ᵀ = 1) ∧
      (unitPivotLeft K * K * unitPivotRightElimination K =
        of (Fin.cases (Fin.cases 1 (fun _ => 0))
          (fun i => Fin.cases 0 (unitPivotSchurComplement K i)))) := by
    have hba := Ring.inverse_mul_cancel (K 0 0) h
    have hLL : unitPivotLeft K * lo (K 0 0) (fun i => K i.succ 0) = 1 := by
      rw [hL K, lo_mul, hba]
      convert lo_one using 2
      funext i
      calc
        -(Ring.inverse (K 0 0) * K i.succ 0) * K 0 0 + K i.succ 0 =
            -(Ring.inverse (K 0 0) * K 0 0) * K i.succ 0 + K i.succ 0 := by ring
        _ = 0 := by rw [hba]; ring
    have hRR : unitPivotRightElimination K *
        (lo 1 (fun j => Ring.inverse (K 0 0) * K 0 j.succ))ᵀ = 1 := by
      rw [hR K, ← Matrix.transpose_mul, lo_mul]
      simp only [mul_one, add_neg_cancel, lo_one, Matrix.transpose_one]
    have hz (i : Fin n) :
        K i.succ 0 + -(Ring.inverse (K 0 0) * K i.succ 0 * K 0 0) = 0 := by
      calc
        _ = -(Ring.inverse (K 0 0) * K 0 0) * K i.succ 0 + K i.succ 0 := by ring
        _ = 0 := by rw [hba]; ring
    have hblock : unitPivotLeft K * K * unitPivotRightElimination K =
        of (Fin.cases (Fin.cases 1 (fun _ => 0))
          (fun i => Fin.cases 0 (unitPivotSchurComplement K i))) := by
      rw [hL K, hR K]
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j
      all_goals simp [lo, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
        unitPivotSchurComplement, hba, hz, sub_eq_add_neg, add_comm]
    exact ⟨hLL, hRR, hblock⟩
  have huL (t : T) : IsUnit (unitPivotLeft (K t)) :=
    IsUnit.of_mul_eq_one _ (hp (K t) (hunit t)).1
  have huR (t : T) : IsUnit (unitPivotRightElimination (K t)) :=
    IsUnit.of_mul_eq_one _ (hp (K t) (hunit t)).2.1
  -- Identify the explicit inverse with the total inverse used in the statement.
  have inverse_eq {s : ℕ} (M N : Matrix (Fin (s + 1)) (Fin (s + 1)) A)
      (hu : IsUnit M) (hMN : M * N = 1) : Ring.inverse M = N := by
    calc
      Ring.inverse M = Ring.inverse M * (M * N) := by rw [hMN, mul_one]
      _ = N := Ring.inverse_mul_cancel_left M N hu
  have hiL (t : T) : Ring.inverse (unitPivotLeft (K t)) =
      lo (K t 0 0) (fun i => K t i.succ 0) :=
    inverse_eq _ _ (huL t) (hp (K t) (hunit t)).1
  have hiR (t : T) : Ring.inverse (unitPivotRightElimination (K t)) =
      (lo 1 (fun j => Ring.inverse (K t 0 0) * K t 0 j.succ))ᵀ :=
    inverse_eq _ _ (huR t) (hp (K t) (hunit t)).2.1
  have clo {s : ℕ} (d : T → A) (c : T → Fin s → A)
      (hd : Continuous d) (hc : ∀ i, Continuous (fun t => c t i))
      (i j : Fin (s + 1)) : Continuous (fun t => lo (d t) (c t) i j) := by
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [lo, of_apply, Fin.cases_zero] using hd
    · simpa only [lo, of_apply, Fin.cases_zero, Fin.cases_succ] using
        (continuous_const : Continuous (fun _ : T => (0 : A)))
    · simpa only [lo, of_apply, Fin.cases_zero, Fin.cases_succ] using hc i
    · exact continuous_const
  refine ⟨huL, huR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp_rw [hL]
    exact clo _ _ hinv (fun i => (hinv.mul (hK i.succ 0)).neg) i j
  · intro i j
    simp_rw [hR]
    exact clo _ _ continuous_const (fun j => (hinv.mul (hK 0 j.succ)).neg) j i
  · intro i j
    simp_rw [hiL]
    exact clo _ _ (hK 0 0) (fun i => hK i.succ 0) i j
  · intro i j
    simp_rw [hiR]
    exact clo _ _ continuous_const (fun j => hinv.mul (hK 0 j.succ)) j i
  · intro i j
    exact (hK i.succ j.succ).sub ((hinv.mul (hK i.succ 0)).mul (hK 0 j.succ))
  · intro t
    exact (hp (K t) (hunit t)).2.2

end Matrix
