/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.MarkedBoundaryOrder
public import Sheaf.AlgebraicGeometry.CommonMarkedTestSequence
public import Sheaf.AlgebraicGeometry.RestrictedMarkedTests
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift
import Sheaf.AlgebraicGeometry.TestSequencePointOrderRecovery
import Sheaf.AlgebraicGeometry.TestSequenceBoundaryOrderRecovery

/-! # Numerical recovery from marked-ideal test sequences

Source: Bierstone--Milman, Functoriality in resolution of singularities,
Theorems 6.1 and 6.2, pp. 631--633; ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-test-sequence-order-recovery).

Equalities of normalized extended orders are expressed by cross-multiplication with
positive marks. This retains rational, rather than truncated natural, normalization
and includes infinite order. The empty common sequence includes the initial assertion.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Test-equivalent marked ideals of equal local support dimension have equal normalized
point orders and boundary orders on common cosupport, after every common finite test.
The three adapted-coordinate conditions express the ordered SNC boundary and its
transversality to both supports; the boundary ideal is the intersection of its members.
Source: BM, Theorems 6.1--6.2, pp. 631--633, referred to by ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-test-sequence-order-recovery).

Proof:
1. Recover cosupport at every prefix from permissible closed-point blowups. Upper
   semicontinuity (lem-trf-logarithmic-differential-transform), smooth point centers
   (lem-trf-generic-center-formal-normal-slice), and Jacobson density
   (lem-sc-lft-over-field-jacobson-space) give equality of the closed subsets.
2. At any point, including a nonclosed point, take the common smooth reduced closure
   and separate normal completions F[[u_1,...,u_n]] of the two supports, with equal n.
   The normal-slice lemma identifies their orders and boundary divisibilities.
3. Adjoin a line t and iterate the section blowups. The controlled ideals are
   t^(-kd) K(t^k u). The marked-controlled-blowup-charts and isotropic-cylinder-order
   lemmas show every such finite tower is permissible, also when K = 0 or n = 0.
4. Test whether the newest exceptional divisor intersected with cosupport has its
   full local dimension n. Smoothness, the regular-local-domain lemma and dimension
   drop by a nonzerodivisor identify this with containment in the dth divisor power.
5. After a successful test blow up that common smooth divisor center, dividing by
   t^d on the support. The chart and normal-slice lemmas justify each actual transform.
6. After i such divisions the next test succeeds exactly when k(m-d) >= (i+1)d
   for finite initial order m, and always for the zero ideal. This determines one
   common set S of successful pairs (k,i), using only permissible prefixes.
7. Its supremum of (i+1)/k is m/d-1: use floor(k(m/d-1))/k for approximation.
   The empty set detects m/d = 1; unbounded quotients detect infinite order.
8. For a boundary through the point, separate zero ideals first. Otherwise their
   finite boundary exponents a,c are identified by the normal-slice lemma.
9. Adjoin a fresh line and repeatedly blow up the intersection of its newest
   exceptional boundary with the chosen boundary. These auxiliary transformations
   use ordinary pullback: u_1 maps to t^k u_1. Coordinate charts and regularity over
   the perfect field Q give smooth supports; the selected points stay in cosupport.
10. Apply point-order recovery to these pairs. The anisotropic-boundary-order lemma
    makes their orders eventually (k+1)a+h_K and (k+1)c+h_L. Subtract the two
    successive finite normalized equalities to obtain a/d = c/b. Missing components
    have order zero by definition.
11. A common prefix leaves equal suffix tests. Smoothness is preserved by the chart
    lemmas. The dimension formula and closed-irreducible dimension/transcendence
    degree lemma preserve equality of local support dimensions: line products add
    one to transcendence degree, surviving strict transforms are birational, and
    both support residue fields equal the ambient residue field. Repeat steps 1--10
    on every transformed common cosupport. -/
theorem test_sequence_order_recovery
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
          order P'.ideal y * (M'.marking : ℕ∞) ∧
        ∀ i : Fin T.boundary.length,
          boundaryOrder M'.ideal ((T.boundary.get i).comap M'.j) x *
              (P'.marking : ℕ∞) =
            boundaryOrder P'.ideal ((T.boundary.get i).comap P'.j) y *
              (M'.marking : ℕ∞) := by
  intro T M' P' hsequence x y hxy hx hy
  exact ⟨
    test_sequence_point_order_recovery S M P hboundary hordered hM hP hdim hequivalent
      T M' P' hsequence x y hxy hx hy,
    test_sequence_boundary_order_recovery S M P hboundary hordered hM hP hdim hequivalent
      T M' P' hsequence x y hxy hx hy⟩

end AlgebraicGeometry.HilbertSamuel
