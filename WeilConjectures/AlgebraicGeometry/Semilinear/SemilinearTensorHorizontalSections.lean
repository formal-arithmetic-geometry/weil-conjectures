/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction

/-! # Pure tensors and the actual horizontal restrictions

Source: Zheng Construction 4.1; Stacks 03EL.
(blueprint: lem-coef-evaluation-tensor-horizontal-pure)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] evaluation transition tensorSection ordinaryEvaluationTensor
attribute [local irreducible] coefficientMap systemRing evalSection rings ringPresheaf
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence Prod.sectR
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] SheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalarsObj
attribute [local implicit_reducible] PresheafOfModules.presheaf ModuleCat.restrictScalars
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end WeilConjectures.SemilinearSections
