/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveLineTrace
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Submission.WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
public import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The supported Ext representative for projective-line integral transport

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, supported diagonal Ext realization.
(auxiliary; not a blueprint node).
The existing construction is separated so each file stays within the compilation limit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

/-- The supported Ext representative with the ordinary functor endpoints fixed.
Source: exact closed direct image and Ext realization in the diagonal calculation.
(auxiliary; not a blueprint node). -/
@[irreducible]
def supportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u})
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    (ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧ :=
  supportedExactDerivedMap
    (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
    (ordinaryFiniteConstant A (ProjectiveLine S))
    (Scheme.finiteEtaleTateLine
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ

end AlgebraicGeometry.Etale.SfP1Transport
