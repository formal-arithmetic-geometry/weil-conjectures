/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Pullback of global sections
Source: the constant-sheaf adjunction and inverse-image units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Etale Scheme.Hom.Etale Scheme.instCategoryEtale
  MorphismProperty MorphismProperty.Comma.instCategory constantEtale twistEtale
  Functor.mapDerivedCategoryPlus DerivedCategory.Plus.homologyFunctor
  Functor.sheafPushforwardContinuous Etale.lowerStar

/-- The section pullback is the mate of the canonical constant-sheaf pullback.
Source: the constant-sheaf adjunction.
(blueprint: aux-lem-pur-coordinate-global-sections-unit). -/
def coordinateGlobalSectionsUnit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) Y ⟶
      Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) X where
  app F :=
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj F).obj.map
        (((Scheme.Etale.isTerminalMkId Y).isTerminalObj f.Etale).uniqueUpToIso
          (Scheme.Etale.isTerminalMkId X)).inv.op
  naturality {F G} b := by
    dsimp
    simp only [Category.assoc]
    rw [← Category.assoc]
    have hu := congrArg (fun z ↦ z.hom.app (op (Scheme.Etale.mk (𝟙 Y))))
      ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) f).unit.naturality b)
    have hu' : b.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} P.Coefficient) f).unit.app G).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) =
      ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) f).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map b).hom.app
          (op ((Scheme.Hom.Etale f).obj (Scheme.Etale.mk (𝟙 Y)))) := by
      exact hu
    let i := ((Scheme.Etale.isTerminalMkId Y).isTerminalObj f.Etale).from
      (Scheme.Etale.mk (𝟙 X))
    have hn := ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map b).hom.naturality
      i.op
    have hu'' := congrArg (fun z ↦ z ≫
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj G).obj.map i.op) hu'
    have hn' := congrArg (fun z ↦
      ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) f).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) ≫ z) hn
    simpa only [Category.assoc, i] using hu''.trans hn'.symm

/-- The canonical pullback comparison between the explicitly specified terminal objects.
Source: preservation of terminal objects by etale base change
(blueprint: aux-lem-pur-coordinate-global-sections-unit). -/
def coordinateTerminalPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.Etale.obj (Scheme.Etale.mk (𝟙 Y)) ≅ Scheme.Etale.mk (𝟙 X) :=
  ((Scheme.Etale.isTerminalMkId Y).isTerminalObj f.Etale).uniqueUpToIso
    (Scheme.Etale.isTerminalMkId X)

/-- The constant-sheaf mate is the inverse-image adjunction unit on terminal
sections, followed by the specified terminal-object pullback isomorphism.
Source: the units defining `upperStarConstantSheafIso`.
Proof: compare evaluation at the chosen and explicit terminal objects by the
constant-presheaf adjunction. Uniqueness of the constant adjunction gives the
chosen-terminal formula. Naturality of the inverse-image unit and uniqueness
of the arrow to its terminal pullback convert it to the explicit formula.
(blueprint: aux-lem-pur-coordinate-global-sections-unit). -/
theorem coordinateGlobalSectionsUnit_eval (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (P.coordinateGlobalSectionsUnit f).app F =
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app
        F).hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj F).obj.map
        (((Scheme.Etale.isTerminalMkId Y).isTerminalObj f.Etale).uniqueUpToIso
          (Scheme.Etale.isTerminalMkId X)).inv.op := by
  unfold coordinateGlobalSectionsUnit
  rfl

/-- Global section pullback carries the constant adjunction unit to the target unit.
Source: the constant-sheaf adjunction.
Proof: the source library computes the inverse-image unit on every sheafified
constant section. Move the constant comparison across terminal restriction by
naturality, then restrict the sheafification unit to the target terminal object.
(blueprint: aux-lem-pur-coordinate-global-sections-unit). -/
theorem coordinateGlobalSectionsUnit_one (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.isTerminalMkId Y)).unit.app (ModuleCat.of P.Coefficient P.Coefficient)) ≫
      (P.coordinateGlobalSectionsUnit f).app (P.constantEtale Y) ≫
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient)) =
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.isTerminalMkId X)).unit.app (ModuleCat.of P.Coefficient P.Coefficient) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let M := ModuleCat.of P.Coefficient P.Coefficient
  let V := Scheme.Etale.mk (𝟙 Y)
  let i := (((Scheme.Etale.isTerminalMkId Y).isTerminalObj f.Etale).uniqueUpToIso
    (Scheme.Etale.isTerminalMkId X)).inv
  have h := Etale.constantSheafUnit_app_toSheafify f M V m
  have hn := (CategoryTheory.toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).naturality i.op
  have h' := congrArg (fun z ↦ (P.constantEtale X).obj.map i.op z) h
  have hs := (ConcreteCategory.congr_hom hn m).symm
  simp only [Functor.const_obj_map, ConcreteCategory.comp_apply] at hs
  simpa [ModuleCat.Hom.hom, M, V, i, constantEtale, constantSheaf, Scheme.Etale.mk,
    coordinateGlobalSectionsUnit,
    Etale.constantSheafUnit, Etale.lowerStar, Functor.sheafPushforwardContinuous, constantSheafAdj,
    constantPresheafAdj, Adjunction.comp_unit_app, Category.assoc,
    ConcreteCategory.comp_apply] using! h'.trans hs

end WeilConjectures.PurityFiniteSetting
