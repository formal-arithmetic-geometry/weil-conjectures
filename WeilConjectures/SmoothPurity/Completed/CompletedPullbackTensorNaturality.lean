/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison

/-! # Naturality of the localized canonical pullback/tensor comparison

Source: Stacks 07A4 and the rationalization paragraph of the blueprint.
(blueprint: lem-pur-canonical-rational-pullback-tensor-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  pullbackTensorCalculus integralDerivedPullback integralCompletedTensor

end WeilConjectures
