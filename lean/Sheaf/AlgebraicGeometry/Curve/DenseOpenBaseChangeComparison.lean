/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# DenseOpenBaseChangeComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-base-change-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-base-change-comparison).

Proof: Form the open-closed short exact sequence with quotient Q = i_* i^* F supported on
the finite set Z of k-rational closed points. Finite direct image and zero-dimensional
cohomology identify H^q(X,Q) with zero for q > 0 and H^0 with the finite product of its
geometric stalks. After any algebraically closed field extension this product is
unchanged, and the canonical pullback map is bijective. Pullback gives an exact sequence
on the base changed curve and a commuting long exact cohomology ladder. If comparison
is bijective for G, the five lemma applied with the comparisons for Q proves it for F.
Conversely, if comparison is bijective for F, the segment H^(q-1)(F) → H^(q-1)(Q) →
H^q(G) → H^q(F) → H^q(Q), with the preceding terms zero in degree zero, and the five lemma
prove bijectivity for G. Properness supplies the comparison hypotheses without a
torsion restriction. In the invertible-order case the required order condition passes
to subobjects and quotients. If F is primary while G has invertible order, G is zero
by geometric stalk conservativity, so every comparison for G is bijective. These are
the two cases in the displayed torsion alternative.
-/
theorem IsCurve.dense_open_baseChange_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : P.IsConstructible)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec G) ∧
    (IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec G) := by sorry

end AlgebraicGeometry
