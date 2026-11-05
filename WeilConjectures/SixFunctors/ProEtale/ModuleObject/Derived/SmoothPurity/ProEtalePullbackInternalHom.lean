/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian

/-! # Internal Hom and weakly etale coefficient pullback

Source: the localization calculation for internal Hom, blueprint stratum Hom step 3.
(blueprint: lem-proetale-pullback-internal-hom)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local irreducible] Mod.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]

end AlgebraicGeometry.ProEtale.CondensedRing
