/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Submission.WeilConjectures.Topology.PresheafModuleStalkFunctor
import Submission.WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import Mathlib.Algebra.Category.Grp.Zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
/-- (blueprint: new-extension-by-zero-outside-stalk) -/
theorem module_extensionByZero_outside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
      IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x) := by
  dsimp
  intro F x hx
  have h := moduleExtensionByZero_stalk_outside X.toRingedSpace U F x hx
  apply (AddCommGrpCat.isZero_iff_subsingleton).mpr
  have hs := (ModuleCat.isZero_iff_subsingleton).mp h
  exact hs
end AlgebraicGeometry.Scheme.Modules
