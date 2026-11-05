/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonAssociativity
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import all WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators

/-! # Normalized natural total tensor pullback comparison
Source: Stacks 03EL and 07A4; signed total tensor, 06YN.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.RingedForgetTensorTransposition
namespace WeilConjectures
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification coefficientTensorGenerator
attribute [local implicit_reducible] coefficientTotalTensor

end WeilConjectures
