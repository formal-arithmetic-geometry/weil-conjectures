/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MarkedBoundaryOrder
public import Sheaf.AlgebraicGeometry.CommonMarkedTestSequence
public import Sheaf.AlgebraicGeometry.RestrictedMarkedTests
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift
import Sheaf.AlgebraicGeometry.TestSequencePointOrderRecovery
import Sheaf.AlgebraicGeometry.BoundaryOrderTestWitnesses
import Mathlib.Tactic

/-! # Boundary orders from two successive test weights

Source: BM, Theorem 6.2, pp. 632--633
(blueprint: lem-trf-test-sequence-boundary-order-recovery).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Recover boundary order by subtracting two finite point-order equalities.
Source: BM, Theorem 6.2, pp. 632--633
(blueprint: lem-trf-test-sequence-boundary-order-recovery).

Proof: The geometric witness theorem supplies either two infinite orders, two zero orders,
or finite boundary exponents a,c with two common test sequences whose point orders are
(k+1)a+h, (k+1)c+l and (k+2)a+h, (k+2)c+l. Point-order recovery applies to both actual
sequences. Marks are unchanged, so subtracting their finite natural equalities cancels
the constant terms and gives a*b=c*d. Cast back to extended naturals. In the infinite case
positivity of both marks preserves infinity, and in the zero case both products vanish. -/
theorem test_sequence_boundary_order_recovery
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
        ∀ i : Fin T.boundary.length,
          boundaryOrder M'.ideal ((T.boundary.get i).comap M'.j) x *
              (P'.marking : ℕ∞) =
            boundaryOrder P'.ideal ((T.boundary.get i).comap P'.j) y *
              (M'.marking : ℕ∞) := by
  intro T M' P' hsequence x y hxy hx hy i
  obtain htop | hzero | ⟨a, c, h, l, k, ha, hc, hw⟩ :=
    boundary_order_test_witnesses S M P hboundary hordered hM hP hdim hequivalent
      T M' P' hsequence x y hxy hx hy i
  · rw [htop.1, htop.2]
    simp [Nat.ne_of_gt M'.positive, Nat.ne_of_gt P'.positive]
  · rw [hzero.1, hzero.2]
    simp
  · have eqs (r : Fin 2) :
        ((k + r.val + 1) * a + h) * P'.marking =
          ((k + r.val + 1) * c + l) * M'.marking := by
      obtain ⟨U, A, B, hseq, hA, hB, z, w, hzw, hz, hw', hordA, hordB⟩ := hw r
      have heq := test_sequence_point_order_recovery S M P
        hboundary hordered hM hP hdim hequivalent U A B hseq z w hzw hz hw'
      rw [hordA, hordB, hA, hB] at heq
      exact_mod_cast heq
    have e0 := eqs 0
    have e1 := eqs 1
    norm_num only [Fin.val_zero, Fin.val_one] at e0 e1
    have hac : a * P'.marking = c * M'.marking := by nlinarith only [e0, e1]
    rw [ha, hc]
    exact_mod_cast hac

end AlgebraicGeometry.HilbertSamuel
