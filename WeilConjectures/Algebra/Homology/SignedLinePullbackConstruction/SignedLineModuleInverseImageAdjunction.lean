/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.InverseImageAction.SignedLineModuleInverseImageAction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.SignedLineSheafPullbackUnitPresentation
import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.SignedLineModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SignedLineSheafPullbackForgetComparison
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
/-! # Restricting the abelian inverse-image adjunction to modules
Source: Stacks Project, Modules on Sites, Tag 03D3.
(blueprint: lem-pur-signed-line-module-inverse-image-adjunction).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLinePullbackConstruction
open CategoryTheory.SignedLinePullbackConstruction
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {A : Sheaf J RingCat.{max u v w}} {B : Sheaf K RingCat.{max u v w}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{max u v w} J K).obj B)
  [(pushforward.{max u v w} φ).IsRightAdjoint]
open MonoidalCategory
variable (hgen : ∀ (M : SheafOfModules.{max u v w} A) (T : Sheaf K (Type (max u v w)))
  (a b : (sheafCompose K (CategoryTheory.forget RingCat.{max u v w})).obj B ⊗
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj
      ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)) ⟶ T),
  (∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
    a.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) =
      b.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) → a = b)

end SheafOfModules.SignedLinePullbackConstruction
