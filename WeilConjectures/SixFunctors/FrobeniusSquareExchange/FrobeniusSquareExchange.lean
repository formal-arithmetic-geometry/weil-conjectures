/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Exchange maps of the Frobenius square

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
 sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: def-weil-frobenius-square-exchange).

The direct exchange is the canonical unit--square--counit mate for a Cartesian square.
The compact-support exchange is formed from the direct exchange for a chosen
compactification and the inverse open-extension exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

namespace FrobeniusSquareExchange

/-- The direct-image exchange for a Cartesian square of scheme isomorphisms.

The mate is the composite `Lf^* Lg_Y^* Rf_* K → Lg_X^* K` with the
canonical pullback-square comparison followed by the counit, as in the source.
Source: paragraph 1 of `lem-fix-weil-operations.proof.md`
(blueprint: def-weil-frobenius-square-exchange).
-/
noncomputable def direct
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {gX : X ⟶ X} {gY : Y ⟶ Y} [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) :
    (AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward Λ.X f ⋙
      AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback Λ.X gY) ⟶
      (AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback Λ.X gX ⋙
        AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward Λ.X f) :=
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedExchange Λ.X sq

end FrobeniusSquareExchange

end WeilConjectures
