/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups X6 and A4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula

/-! # The supported Ext representative for projective-line integral transport

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, supported diagonal Ext realization.
(blueprint: def-sf-p1-supported-ext-map-data).
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
(blueprint: def-sf-p1-supported-ext-map-data). -/
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
