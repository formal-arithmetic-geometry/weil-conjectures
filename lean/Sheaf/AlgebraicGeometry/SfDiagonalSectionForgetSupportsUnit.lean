/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R8
-/
module

public import Sheaf.AlgebraicGeometry.SfP1IntegralTransportData
public import Sheaf.AlgebraicGeometry.OrdinaryProperForgetComparison

/-! # Unit-coefficient diagonal forget-supports normalization

This is the coefficient-free special case used to prove the natural formula in
`SfDiagonalSectionForgetSupports` (blueprint: lem-sf-diagonal-section-forget-supports-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The diagonal section normalization for the tensor unit and its identity map.

Source: blueprint latest, `thm-amb-p1-adjunction.proof.md`, the equation
`M = Rp₂_* Δ_* M` for the constant object.  Expand the selected compact-support
compositor for `Δ` followed by either projection, apply the canonical proper
forget-supports comparisons, and use the composition-unit identity for the
ordinary direct-image adjunction.  The two Boolean cases use `diagonal_fst` and
`diagonal_snd`; this is the coefficient-free core of the natural statement.
(blueprint: lem-sf-diagonal-section-forget-supports-unit). -/
theorem diagonalSection_forgetSupports_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (a : Bool) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          ((ordinaryProperForgetComparison A
              (TraceDiagonalDatum.diagonal f)).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
            (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
              (𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))) ≫
        (ordinaryProperForgetComparison A
          (projection f a)).hom.app
            ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).obj
              (derivedTensorUnit (ModuleCat.{u + 1} A) X)) =
      (constantUnit A X).inv ≫ supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            ((constantUnit A X).hom ≫
              𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))) := by
  sorry

end AlgebraicGeometry.Etale.SfP1Transport
