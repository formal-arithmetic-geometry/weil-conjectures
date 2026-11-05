/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization

/-! # The unit equation for the mate of pullback composition

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-mate-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback schemeHomPullbackAdjunction
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Adjunction.comp DerivedCategory.Qh

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

end AlgebraicGeometry
