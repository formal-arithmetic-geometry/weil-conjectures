module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.Subgroup.Saturated
public import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Fractional column descent in a root saturated additive monoid

Source: Stacks Project, Algebra, Tag 0F0K, for determinant context; ILO, Travaux de
Gabber, VIII 3.1.17, printed p. 101, for saturation. The denominator and determinant
descent argument is agent-supplied.
(blueprint: lem-trf-saturated-monoid-fractional-column-descent)
-/

@[expose] public section

namespace AddSubmonoid

private theorem integral_combination_mem
    {r : ℕ} (S : AddSubmonoid (Fin r → ℤ)) (hS : S.NSMulSaturated)
    (A : Matrix (Fin r) (Fin r) ℤ) (hcols : ∀ i, (fun k ↦ A k i) ∈ S)
    (a : Fin r → ℚ) (ha : ∀ i, 0 ≤ a i) (x : Fin r → ℤ)
    (hx : ∀ k, (x k : ℚ) = ∑ i, a i * (A k i : ℚ)) : x ∈ S := by
  classical
  let N : ℕ := ∏ i, (a i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  have hb : ∀ i, ∃ b : ℕ, (N : ℚ) * a i = b := by
    intro i
    have hd : (a i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨d, hd⟩ := hd
    refine ⟨d * (a i).num.toNat, ?_⟩
    have hn : ((a i).num.toNat : ℤ) = (a i).num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.mpr (ha i))
    have hnq : ((a i).num.toNat : ℚ) = ((a i).num : ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℚ)) hn
    have hden : ((a i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (a i).den_nz
    have hnum : a i * ((a i).den : ℚ) = ((a i).num : ℚ) :=
      (eq_div_iff hden).mp (Rat.num_div_den (a i)).symm
    rw [hd, Nat.cast_mul, Nat.cast_mul, hnq]
    calc
      ((a i).den : ℚ) * d * a i = d * (a i * ((a i).den : ℚ)) := by ac_rfl
      _ = d * ((a i).num : ℚ) := by rw [hnum]
  choose b hb using hb
  have hclear : N • x = ∑ i, b i • (fun k ↦ A k i) := by
    funext k
    simp only [Finset.sum_apply]
    change N • x k = ∑ i, b i • A k i
    simp only [nsmul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum]
    rw [hx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hb i, mul_assoc]
  have hmem : N • x ∈ S := by
    rw [hclear]
    exact S.sum_mem (fun i _ ↦ S.nsmul_mem (hcols i) (b i))
  exact (hS hmem).resolve_left (Nat.ne_of_gt hN)

/-- An integral nonnegative rational combination of columns in a root saturated
submonoid of the integer lattice belongs to that submonoid. Replacing a column
whose coefficient is positive multiplies the determinant by that coefficient and
strictly decreases its positive absolute value when all coefficients are below one.

Source: Stacks Project, Algebra, Tag 0F0K, for determinant context; ILO, Travaux de
Gabber, VIII 3.1.17, printed p. 101, for the saturation convention. The ambient-lattice
saturation hypothesis and the following argument are explicit in the DAG node.
(blueprint: lem-trf-saturated-monoid-fractional-column-descent)

Proof: Write each coefficient as `p_i / q_i`, with `q_i > 0` and `p_i ≥ 0`.
The product `N` of the denominators is positive, and each `N * a_i` is a natural
number `b_i`. Clearing denominators in the coordinatewise equality yields
`N • x = ∑ i, b_i • v_i` in the integer lattice, since its inclusion in the
rational lattice is injective. Closure under zero and addition puts the right
side in `S`. Root saturation gives `x ∈ S`. Thus every column of `A.updateCol j x`
lies in `S`. Compute its determinant over the rationals using the Leibniz formula
of def-weil-pbc-matrix-determinant: distributing the combination in column `j`
gives the sum of `a_i` times the determinants with column `j` replaced by column `i`.
For `i ≠ j`, lem-weil-pbc-det-repeated-column-zero makes that determinant zero;
for `i = j` it is the original determinant. Integer determinants commute with
the inclusion into the rationals, giving the stated identity. Finally
`0 < a_j < 1` and `det A ≠ 0` imply the absolute-value identity and both strict
inequalities. If every coefficient is zero, `x = 0 ∈ S` and no replacement is
required. -/
theorem saturated_fractional_column_descent
    {r : ℕ} (hr : 1 ≤ r) (S : AddSubmonoid (Fin r → ℤ))
    (hS : S.NSMulSaturated) (A : Matrix (Fin r) (Fin r) ℤ)
    (hcols : ∀ i : Fin r, (fun k ↦ A k i) ∈ S) (hdet : A.det ≠ 0)
    (a : Fin r → ℚ) (ha : ∀ i : Fin r, 0 ≤ a i ∧ a i < 1)
    (x : Fin r → ℤ)
    (hx : ∀ k : Fin r, (x k : ℚ) = ∑ i : Fin r, a i * (A k i : ℚ)) :
    x ∈ S ∧ ∀ j : Fin r, 0 < a j →
      (∀ i : Fin r, (fun k ↦ (A.updateCol j x) k i) ∈ S) ∧
      ((A.updateCol j x).det : ℚ) = a j * (A.det : ℚ) ∧
      0 < abs ((A.updateCol j x).det : ℚ) ∧
      abs ((A.updateCol j x).det : ℚ) = a j * abs (A.det : ℚ) ∧
      abs ((A.updateCol j x).det : ℚ) < abs (A.det : ℚ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hxS : x ∈ S := integral_combination_mem S hS A hcols a (fun i ↦ (ha i).1) x hx
  refine ⟨hxS, ?_⟩
  intro j hj
  have hcols' : ∀ i : Fin (n + 1), (fun k ↦ (A.updateCol j x) k i) ∈ S := by
    intro i
    by_cases hij : i = j
    · simpa [hij] using hxS
    · simpa [Matrix.updateCol_apply, hij] using hcols i
  have hid : ((A.updateCol j x).det : ℚ) = a j * (A.det : ℚ) := by
    have hmat : ((A.updateCol j x).map (fun z : ℤ ↦ (z : ℚ))) =
        (A.map (fun z : ℤ ↦ (z : ℚ))).updateCol j
          (fun k ↦ ∑ i, a i • (A.map (fun z : ℤ ↦ (z : ℚ))) k i) := by
      funext k i
      by_cases hij : i = j
      · simp only [Matrix.map_apply, Matrix.updateCol_apply, hij, ↓reduceIte,
          smul_eq_mul, hx]
      · simp only [Matrix.map_apply, Matrix.updateCol_apply, hij, ↓reduceIte]
    rw [Int.cast_det, hmat, Matrix.det_updateCol_sum]
    simp only [smul_eq_mul, ← Int.cast_det]
  have hdetq : (A.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  have hpos : 0 < abs (A.det : ℚ) := abs_pos.mpr hdetq
  have habs : abs ((A.updateCol j x).det : ℚ) = a j * abs (A.det : ℚ) := by
    rw [hid, abs_mul, abs_of_pos hj]
  refine ⟨hcols', hid, ?_, habs, ?_⟩
  · rw [habs]
    exact mul_pos hj hpos
  · rw [habs]
    simpa only [one_mul] using mul_lt_mul_of_pos_right (ha j).2 hpos

end AddSubmonoid
