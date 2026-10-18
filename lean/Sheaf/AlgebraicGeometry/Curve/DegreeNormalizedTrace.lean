/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.SecondKummerDivisors
import Sheaf.AlgebraicGeometry.DivisorClassCurve

/-! # The degree-normalized finite trace on a proper curve

Source: Milne, Lectures on Etale Cohomology, Proposition 14.2, Proposition 14.5,
and Remark 14.6. (blueprint: def-wf-degree-normalized-curve-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The Picard class of O(P), using the dual point ideal. This is the point divisor
class of def-sc-divisor, not a chosen line bundle. Source: Milne Remark 14.6 and
Curve.Picard, Pic.ofClosedPoint. (blueprint: def-wf-degree-normalized-curve-trace) -/
def tracePointPic (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] (P : closedPoints C) : C.Pic :=
  letI : C.Over (Spec (.of k)) := ⟨f⟩
  letI : ConnectedSpace C := IsConnectedCurve.connectedSpace' f
  letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  letI : IsRegular C := IsRegular.of_smooth f
  letI : IsIntegral C := IsRegular.isIntegral C
  letI : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  Pic.ofClosedPoint k P

/-- Existence and uniqueness of the degree-normalized trace.
Source: Milne Proposition 14.2, Proposition 14.5, Remark 14.6.
(blueprint: def-wf-degree-normalized-curve-trace)
Proof: ell is invertible on C because it differs from the field characteristic.
The second Kummer sequence identifies H2(mu_(ell^n)) with Pic(C)/(ell^n).
Degree modulo ell^n descends to this quotient. Pic^0(C) is ell-divisible (the
Jacobian multiplication map is surjective over the algebraically closed field),
so degree gives the canonical isomorphism to Z/(ell^n). Each closed point has
residue field k and degree one, hence its Kummer class has trace one. Conversely,
every Picard class is represented by a divisor, a finite integral sum of closed
points. Their Kummer classes generate H2, so any additive map with these values
is this degree map. The Kummer boundary is independent of the proof of invertibility. -/
theorem existsUnique_degreeNormalizedCurveTrace
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (ell c : ℕ) [Fact ell.Prime] [CharP k c] (hell : ell ≠ c)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃! tr : Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 2 →+ ZMod (ell ^ n),
      ∀ (hunit : IsUnit ((ell ^ n : ℕ) : Γ(C, ⊤))) (P : closedPoints C),
        tr (C.kummerδ₁ (ell ^ n) hunit
          (Pic.toCohomologicalPicardGroupAddEquiv C
            (Additive.ofMul (tracePointPic k C f P)))) = 1 := by
  sorry

/-- The unique additive map taking every point's Kummer class to one. Its data is
fixed by the uniqueness theorem; no arbitrary trace map is selected.
Source: Milne Proposition 14.5 and Remark 14.6.
(blueprint: def-wf-degree-normalized-curve-trace) -/
def degreeNormalizedCurveTrace
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (ell c : ℕ) [Fact ell.Prime] [CharP k c] (hell : ell ≠ c)
    (n : ℕ) (hn : 1 ≤ n) :
    Sheaf.H (C.rootsOfUnitySheaf (ell ^ n)) 2 →+ ZMod (ell ^ n) :=
  Classical.choose
    (existsUnique_degreeNormalizedCurveTrace k C f ell c hell n hn).exists

end AlgebraicGeometry.Scheme
