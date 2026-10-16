/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module
public import Sheaf.CategoryTheory.ModuleInverseImageAction
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.CategoryTheory.SheafPullbackUnitPresentation
import Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import all Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
/-! # Restricting the abelian inverse-image adjunction to modules
Source: Stacks Project, Modules on Sites, Tag 03D3.
(blueprint: lem-weil-pbc-module-inverse-image-action-adjunction).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
open MonoidalCategory
private noncomputable def scalarAction (M : SheafOfModules.{u} B) :
    (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf B).obj M) ⟶
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf B).obj M) :=
  ⟨{ app := fun U ↦ ↾fun x ↦
       @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x.1 x.2
     naturality := by
       intro U V i
       ext x
       exact (M.val.map_smul i x.1 x.2).symm }⟩
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
private theorem linear_of_adjunct_linear
    (M : SheafOfModules.{u} A) (N : SheafOfModules.{u} B)
    (a : InverseImageAction φ M)
    (α : (sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M) ⟶
      (toSheaf B).obj N)
    (hβ : ∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
      ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).homEquiv _ _ α).hom.app U
        (r • m) =
        @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
          (φ.hom.app U r)
          (((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).homEquiv _ _ α).hom.app U m)) :
    ∀ (V : Dᵒᵖ) (r : B.obj.obj V) (m : a.toModule.val.obj V),
      α.hom.app V (r • m) =
        @SMul.smul (B.obj.obj V) (N.val.obj V) inferInstance r (α.hom.app V m) := by
  let t := (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map α
  have hmaps : scalarAction a.toModule ≫ t =
      (𝟙 _ ⊗ₘ t) ≫ scalarAction N := by
    apply hgen M
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf B).obj N))
      (scalarAction a.toModule ≫ t) ((𝟙 _ ⊗ₘ t) ≫ scalarAction N)
    intro U r m
    change α.hom.app (F.op.obj U)
      ((show B.obj.obj (F.op.obj U) from φ.hom.app U r) •
        (show a.toModule.val.obj (F.op.obj U) from
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) = _
    rw [← a.unit_smul U r m]
    exact hβ U r m
  intro V r m
  exact congrArg (fun q ↦ q.hom.app V (r, m)) hmaps
include hgen in
/-- Identify module pullback after constructing its action and testing scalar maps on units.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-inverse-image-action-adjunction).
Proof: The unit is linear by the action hypothesis. The scalar-pair testing property
shows that an abelian map is linear whenever its adjunct is linear: compare its two
scalar-action composites on pairs of unit sections. Lift the abelian inverse-image
maps using this criterion. Faithfulness proves the functor laws. The abelian hom
bijection restricts to linear maps in both directions, naturally. This gives a module
adjunction to the specified scalar-restricted pushforward. Uniqueness of left adjoints
identifies it with Mathlib's pullback. Forgetting gives the stated comparison. -/
private theorem inverseImage_underlying_of_actions
    (actions : ∀ M : SheafOfModules.{u} A, InverseImageAction φ M) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M : SheafOfModules.{u} A,
        (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
          (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
            (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
              ((toSheaf A).obj M) := by
  sorry
/-- A ring unit presenting the set inverse image identifies the underlying module pullback.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-inverse-image-action-adjunction).
Proof: the canonical abelian/set comparison is compatible with its unit. Pair this
presentation with the given ring presentation. It both constructs scalar actions and
shows that linearity can be tested on unit pairs. Apply the restricted adjunction
comparison proved above. The unit equation for leftAdjointUniq identifies the chosen
module unit, followed by this comparison, with the original abelian unit. -/
theorem inverseImage_underlying_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M : SheafOfModules.{u} A,
        (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
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
  apply inverseImage_underlying_of_actions φ
    (fun M Z a b h ↦ ?_) (fun M ↦ Classical.choice
      (inverseImageAction_of_presentations φ M pr hr (pa M) rfl))
  apply (pr.tensor (pa M)).hom_ext a b
  intro U x
  change a.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2) =
    b.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2)
  rw [hr]
  exact h U x.1 x.2

end SheafOfModules
