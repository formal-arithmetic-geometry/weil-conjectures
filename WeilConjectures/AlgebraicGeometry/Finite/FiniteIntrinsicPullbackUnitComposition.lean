/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Unit sections of composite intrinsic finite pullback

Source: Stacks 00YV, composite adjunctions and inverse image on module sheaves
(blueprint: lem-pur-finite-intrinsic-pullback-unit-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.ProEt
  CategoryTheory.MorphismProperty
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme

section Transport
attribute [-instance] CategoryTheory.catToReflQuiver
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

section Definitions
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

end Definitions

attribute [local implicit_reducible] trFunctor trIso trComp trAdj

attribute [local implicit_reducible] untransportRight

end Transport

attribute [local implicit_reducible] trFunctor trIso trComp trAdj untransportRight
  sfIntrinsicTransport sfIntrinsicTransportIso sfIntrinsicTransportComp

attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
