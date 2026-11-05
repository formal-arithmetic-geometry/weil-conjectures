/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorAssociatorDetection

/-! # Associativity of ordinary pro-étale tensor pullback
Source: Stacks 03EL and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction SheafOfModules.tensorObjIsoSheafification
  proEtaleOrdinaryTensorPullback proEtaleRingModuleAdjunction

end WeilConjectures
