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

/-!
# DenseOpenFinitenessComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-finiteness-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-finiteness-comparison).

Proof: The reduced closed complement Z is a finite set of k-rational points. In the open-closed
short exact sequence the third term Q = i_* i^* F has zero positive cohomology and finite
H^0, since its stalks are quotients of the finite constructible stalks of F. In degrees
at least two the first and middle terms have isomorphic cohomology. In degrees zero and
one the exact sequence is 0 → H^0(G) → H^0(F) → H^0(Q) → H^1(G) → H^1(F) → 0.
For either proper constructible finiteness or invertible-order constructible finiteness,
this exact sequence transfers finiteness from G to F: subgroups, quotients and extensions
of finite groups are finite. In the reverse direction it transfers finiteness from F
to G by the same argument and the finite H^0(Q). Constructibility of F is the assumption
hP, transported to the module coefficient encoding. For invertible-order finiteness in
the reverse direction, if F is primary and G has invertible order then G is zero by
stalk conservativity; otherwise the assumed torsion alternative gives invertible order
of F. All arguments apply to empty Z and the zero sheaf.
-/
theorem IsCurve.dense_open_finiteness_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : P.IsConstructible)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) G k →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) F k) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) F k →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) G k) ∧
    (IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec G) := by sorry

end AlgebraicGeometry
