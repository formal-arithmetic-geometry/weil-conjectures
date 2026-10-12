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
# DenseOpenRestrictionComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-restriction-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-restriction-comparison).

Proof: Let a : W → X be any open immersion. Intersecting the dense open U with W leaves a
dense open with finite zero-dimensional complement. The open-closed sequence on X
and its restriction to W therefore identify H^2(G) with H^2(F), both on X and on W.
The pullback long exact ladder makes these identifications commute with restriction
along a. Surjectivity transports in both directions across this square of additive
equivalences: lift the corresponding class through the surjective restriction map,
then through the inverse horizontal equivalence; commutativity and injectivity of the
other horizontal equivalence give the required equality. Since a was arbitrary this
proves exactly the equivalence of the two restriction predicates.
-/
theorem IsCurve.dense_open_restriction_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : P.IsConstructible)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) F ↔
      IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) G := by sorry

end AlgebraicGeometry
