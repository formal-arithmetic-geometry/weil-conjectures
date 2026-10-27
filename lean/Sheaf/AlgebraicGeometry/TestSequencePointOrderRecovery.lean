/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CommonMarkedTestSequence
public import Sheaf.AlgebraicGeometry.RestrictedMarkedTests
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift
import Sheaf.AlgebraicGeometry.CylinderTestThresholds
import Mathlib.Tactic

/-! # Numerical point-order recovery

Source: Bierstone--Milman, Theorem 6.1, pp. 631--632, and step 7 of the
numerical recovery plan (blueprint: lem-trf-test-sequence-point-order-recovery).
The cylinder construction is separated from the proved extended-natural arithmetic.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

private theorem finite_order_le_of_tests (m n d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (hn : b ≤ n)
    (htests : ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (k + i + 1) * d ≤ k * m ↔ (k + i + 1) * b ≤ k * n) :
    m * b ≤ n * d := by
  by_contra h
  have hlt : n * d + 1 ≤ m * b := by omega
  have hbase : d * b ≤ n * d := by nlinarith
  have hsub := Nat.sub_add_cancel hbase
  have hleft : (d * b + (n * d - d * b) + 1) * d ≤ (d * b) * m := by
    nlinarith [Nat.mul_le_mul_left d hlt]
  have hright := (htests (d * b) (Nat.mul_pos hd hb) (n * d - d * b)).mp hleft
  nlinarith

private theorem order_eq_of_tests (m n : ℕ∞) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (hm : (d : ℕ∞) ≤ m) (hn : (b : ℕ∞) ≤ n)
    (htests : ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (((k + i + 1) * d : ℕ) : ℕ∞) ≤ (k : ℕ∞) * m ↔
      (((k + i + 1) * b : ℕ) : ℕ∞) ≤ (k : ℕ∞) * n) :
    m * (b : ℕ∞) = n * (d : ℕ∞) := by
  induction m using ENat.recTopCoe with
  | top =>
    induction n using ENat.recTopCoe with
    | top => simp [Nat.ne_of_gt hd, Nat.ne_of_gt hb]
    | coe n =>
      have h := (htests 1 (by omega) n).mp (by simp)
      have hbad : (1 + n + 1) * b ≤ 1 * n := by exact_mod_cast h
      have : False := by nlinarith
      exact this.elim
  | coe m =>
    induction n using ENat.recTopCoe with
    | top =>
      have h := (htests 1 (by omega) m).mpr (by simp)
      have hbad : (1 + m + 1) * d ≤ 1 * m := by exact_mod_cast h
      have : False := by nlinarith
      exact this.elim
    | coe n =>
      have hm' : d ≤ m := by exact_mod_cast hm
      have hn' : b ≤ n := by exact_mod_cast hn
      have htests' : ∀ k : ℕ, 0 < k → ∀ i : ℕ,
          (k + i + 1) * d ≤ k * m ↔ (k + i + 1) * b ≤ k * n := by
        intro k hk i
        simpa only [← ENat.natCast_mul, ENat.natCast_le_natCast] using htests k hk i
      have hle := finite_order_le_of_tests m n d b hd hb hn' htests'
      have hge := finite_order_le_of_tests n m b d hb hd hm'
        (fun k hk i ↦ (htests' k hk i).symm)
      exact_mod_cast (Nat.le_antisymm hle hge)

private theorem marking_le_order {k : Type u} [Field k] {T : Embedded k}
    (M : Marked T) (x : M.N) (hx : M.j x ∈ M.cosupport) :
    (M.marking : ℕ∞) ≤ order M.ideal x := by
  let := M.closed
  obtain ⟨z, hz, heq⟩ := hx
  have hzx : z = x := M.j.isClosedEmbedding.injective heq
  simpa [hzx] using hz

/-- Recover normalized point orders from the common cylinder divisor tests.
Source: BM, Theorem 6.1, pp. 631--632
(blueprint: lem-trf-test-sequence-point-order-recovery).

Proof: Cosupport supplies m >= d and n >= b. The cylinder comparison supplies the same
inequalities (k+i+1)d <= km and (k+i+1)b <= kn. If just one order is infinite, k=1
and i equal to the other finite order contradict positivity of its mark. If both are
infinite, positive marks preserve infinity. For finite m,n, if nd < mb, choose k=db
and i=nd-db, which is natural since n>=b. The first inequality holds and the second
fails. Interchange the two data to rule out mb<nd. Thus mb=nd, including the boundary
case of normalized order one where no divisor test succeeds. -/
theorem test_sequence_point_order_recovery
    (S : Embedded (ULift.{u} ℚ)) (M P : Marked S)
    [LocallyOfFiniteType S.p] [QuasiCompact S.p]
    (hboundary : IsStrictNormalCrossingsBoundary
      (⨅ i : Fin S.boundary.length, S.boundary.get i))
    (hordered : HasAdaptedNormalCrossingsCenter (⊥ : S.Z.IdealSheafData)
      (fun i ↦ S.boundary.get i))
    (hM : HasAdaptedNormalCrossingsCenter (⊥ : M.N.IdealSheafData)
      (fun i ↦ (S.boundary.get i).comap M.j))
    (hP : HasAdaptedNormalCrossingsCenter (⊥ : P.N.IdealSheafData)
      (fun i ↦ (S.boundary.get i).comap P.j))
    (hdim : ∀ (x : M.N) (y : P.N), M.j x = P.j y →
      ringKrullDim (M.N.presheaf.stalk x) = ringKrullDim (P.N.presheaf.stalk y))
    (hequivalent : RestrictedEquivalent M P) :
    ∀ (T : Embedded (ULift.{u} ℚ)) (M' P' : Marked T),
      CommonTestSequence M P M' P' →
      ∀ (x : M'.N) (y : P'.N), M'.j x = P'.j y →
        M'.j x ∈ M'.cosupport → P'.j y ∈ P'.cosupport →
        order M'.ideal x * (P'.marking : ℕ∞) =
          order P'.ideal y * (M'.marking : ℕ∞) := by
  intro T M' P' hsequence x y hxy hx hy
  exact order_eq_of_tests (order M'.ideal x) (order P'.ideal y)
    M'.marking P'.marking M'.positive P'.positive
    (marking_le_order M' x hx) (marking_le_order P' y hy)
    (cylinder_test_thresholds S M P hboundary hordered hM hP hdim hequivalent
      T M' P' hsequence x y hxy hx hy)

end AlgebraicGeometry.HilbertSamuel
