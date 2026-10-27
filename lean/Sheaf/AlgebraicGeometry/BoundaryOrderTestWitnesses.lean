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

/-! # Two successive boundary-weight tests

Source: BM, Theorem 6.2, pp. 632--633, and numerical recovery steps 8--11
(blueprint: lem-trf-boundary-order-test-witnesses).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Infinite boundary orders agree; finite boundary orders are the slopes of two actual
common exceptional-intersection tests. The witnesses retain the common ambient points,
cosupport membership, marking preservation, and the exact finite point orders.
Source: BM, Theorem 6.2, pp. 632--633; the agent anisotropic-chart refinement in steps 8--11
of numerical recovery (blueprint: lem-trf-boundary-order-test-witnesses).

Proof: Common prefixes preserve suffix equivalence, smoothness, finite type, transverse
ordered boundary coordinates, and equal local support dimensions by the chart and dimension
lemmas. At the chosen common point use the simultaneous normal-slice comparison, so boundary
divisibility agrees with divisibility by the corresponding formal parameter. Point-order
recovery distinguishes zero ideals: a zero completed ideal has infinite point order, and a
nonzero completed ideal has finite point order. Thus a zero ideal on one support forces a
zero ideal on the other; both boundary orders through the point are infinite. If the labelled
component misses the point, it misses on both supports and the separate zero branch holds.
For nonzero ideals along a present component, factor the completed
ideals as u_1^a K and u_1^c L with nonzero restrictions of K,L to u_1=0. Their boundary orders
are a,c. Adjoin a line with zero section, then repeatedly blow up the intersection of its
newest exceptional boundary and the chosen boundary. In the t chart this is u_1 -> t^k u_1,
with ordinary pullback of the ideals. The permissible charts give smooth supports, ordered
boundary labels, unchanged marks, and points over the same ambient point. Total order never
decreases, so these points remain in cosupport. The anisotropic calculation gives constants
h,l and exact orders (k+1)a+h and (k+1)c+l for all sufficiently large k. Choose one such k
and its successor. Concatenate these two finite test words to the current common prefix.
The resulting witnesses contain only actual tests and finite point orders, not the desired
normalized boundary-order equality. -/
theorem boundary_order_test_witnesses
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
          (boundaryOrder M'.ideal ((T.boundary.get i).comap M'.j) x = ⊤ ∧
            boundaryOrder P'.ideal ((T.boundary.get i).comap P'.j) y = ⊤) ∨
          (boundaryOrder M'.ideal ((T.boundary.get i).comap M'.j) x = 0 ∧
            boundaryOrder P'.ideal ((T.boundary.get i).comap P'.j) y = 0) ∨
          ∃ a c h l k : ℕ,
            boundaryOrder M'.ideal ((T.boundary.get i).comap M'.j) x = (a : ℕ∞) ∧
            boundaryOrder P'.ideal ((T.boundary.get i).comap P'.j) y = (c : ℕ∞) ∧
            ∀ r : Fin 2, ∃ (U : Embedded (ULift.{u} ℚ)) (A B : Marked U),
              CommonTestSequence M P A B ∧
              A.marking = M'.marking ∧ B.marking = P'.marking ∧
              ∃ (z : A.N) (w : B.N),
                A.j z = B.j w ∧ A.j z ∈ A.cosupport ∧ B.j w ∈ B.cosupport ∧
                order A.ideal z = (((k + r.val + 1) * a + h : ℕ) : ℕ∞) ∧
                order B.ideal w = (((k + r.val + 1) * c + l : ℕ) : ℕ∞) := by
  sorry

end AlgebraicGeometry.HilbertSamuel
