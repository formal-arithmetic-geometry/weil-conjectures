/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.SheafPullbackUnitPresentation
import Sheaf.CategoryTheory.ModuleInverseImageAction
import all Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import all Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

/-! Unit compatibility for module inverse-image comparisons. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
open MonoidalCategory
variable (hgen : ∀ (M : SheafOfModules.{u} A) (T : Sheaf K (Type u))
  (a b : (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M)) ⟶ T),
  (∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
    a.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) =
      b.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) → a = b)
include hgen in
private theorem inverseImage_underlying_unit_of_actions
    (actions : ∀ M : SheafOfModules.{u} A, InverseImageAction φ M) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
        toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
          (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M) := by
  sorry



/-- The underlying module inverse image comparison respects the adjunction unit.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-inverse-image-unit-comparison).
Proof: use the ring and abelian unit presentations to construct the scalar action
on the actual abelian inverse image. Unit generators detect linearity of adjoints.
The restricted adjunction therefore has the abelian unit as its underlying unit.
Uniqueness of left adjoints compares the chosen module pullback with this lift;
the unit equation for that comparison gives the asserted equation. -/
theorem inverseImage_underlying_unit_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
        (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
          ((toSheaf A).obj M) := by
  let ea := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{u})
  let pa (M : SheafOfModules.{u} A) : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf A).obj M))
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M))) :=
    { unit := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
        ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app ((toSheaf A).obj M))
      iso := ea.app ((toSheaf A).obj M)
      equation := fun U x ↦ by
        have h := sheafPullbackForgetIso_unit J K F
          (CategoryTheory.forget AddCommGrpCat.{u}) ((toSheaf A).obj M)
        exact congrArg (fun t ↦ t.hom.app U x) h }
  apply inverseImage_underlying_unit_of_actions φ
    (fun M Z a b h ↦ ?_) (fun M ↦ Classical.choice
      (inverseImageAction_of_presentations φ M pr hr (pa M) rfl))
  apply (pr.tensor (pa M)).hom_ext a b
  intro U x
  change a.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2) =
    b.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2)
  rw [hr]
  exact h U x.1 x.2

end SheafOfModules
