/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI

/-! # The canonical exchange used in the refinement boundary calculation

Source: `def-exchange-projection`, direct-image exchange formula.
(blueprint: def-sp-original-coefficient-refinement-exchange)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] coefficientProfiniteEssentiallySmall

/-- The mate of the canonical pullback compositor, for ordinary internal modules.

Source: `def-exchange-projection`, displayed definition of Ex_*.
The definition inserts the unit of the base-changed adjunction, applies the
pullback-composition comparison under direct image, and contracts the original
counit. It imposes no coefficient, constructibility or geometric hypotheses.
(blueprint: def-sp-original-coefficient-refinement-exchange) -/
def refinementAmbientExchange
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {V W V' W' : Scheme.{u}} {f : V ⟶ W} {g : W' ⟶ W}
    {f' : V' ⟶ W'} {g' : V' ⟶ V}
    (sq : ChosenCartesianSquare g' f' f g) :
    coefficientDerivedLowerStar R f ⋙ coefficientDerivedUpperStar R g ⟶
      coefficientDerivedUpperStar R g' ⋙ coefficientDerivedLowerStar R f' :=
  (mateEquiv (coefficientDerivedAdjunction R f)
    (coefficientDerivedAdjunction R f')
    (TwoSquare.mk _ _ _ _ (coefficientAmbientSquare R sq.toCommSq).hom)).natTrans

end AlgebraicGeometry.ProEtale.CondensedRing
