/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Localized underived counits and the derived composition comparison
Source: Stacks Project, Tags 0096, 079W and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-localized-counit).
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
attribute [local irreducible] Scheme.Modules.tensorPullback DerivedCategory.Qh
  canonicalDerivedPullbackComposition
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian HomotopyCategory DerivedCategory
  Functor.mapHomologicalComplex Functor.mapHomotopyCategory HomotopyCategory.quotient
  HomologicalComplexUpToQuasiIso.Qh

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

end AlgebraicGeometry
