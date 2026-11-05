/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex

/-! # Counit calculations for pullback composition
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-direct-image-pasted-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Adjunction.comp
  Scheme.Modules.tensorPullback DerivedCategory.Qh

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

end AlgebraicGeometry
