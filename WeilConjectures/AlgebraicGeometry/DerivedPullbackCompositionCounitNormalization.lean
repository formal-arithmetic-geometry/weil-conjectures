/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization

/-! # Counit calculations for pullback composition
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
-- Compare the recorded functors through their interfaces, without unfolding the
-- chosen resolutions or adjunction witnesses during statement elaboration.
-- Open the pinned adjunction explicitly only at its defining Hom equation.
attribute [local irreducible] Scheme.Modules.tensorPullback
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh canonicalDerivedPullbackComposition schemeHomPullbackAdjunction
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

end AlgebraicGeometry
