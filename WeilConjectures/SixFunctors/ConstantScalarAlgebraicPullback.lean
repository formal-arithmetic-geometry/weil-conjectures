/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement

/-! # Algebraic presentation of fixed-scalar inverse image

Source: Stacks Project, Modules on Sites, Tags 03CY and 03D2; Sites, Tag 00YV.
-/

@[expose] public section
set_option autoImplicit false
universe w
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Functor.sheafPullbackConstruction
namespace CategoryTheory.ConstantScalarRestriction

noncomputable section

variable {C D : Type w} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]

private abbrev base (J : GrothendieckTopology C) (A : Type w) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (ring J A)

private def scalar (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    (U : Cᵒᵖ) (a : A) : (ring J A).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a

private def coefficientMap (A : Type w) [CommRing A] :
    ring J A ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J K).obj (ring K A) :=
  ((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _).symm
    { app := fun U ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U)
      naturality := fun _ _ f ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).naturality (F.op.map f) }

omit [RepresentablyFlat F] in
private theorem coefficientMap_scalar (A : Type w) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (coefficientMap J K F A).hom.app U (scalar J A U a) = scalar K A (F.op.obj U) a := by
  have h' := ((sheafificationAdjunction J CommRingCat.{w}).homEquiv
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{w} J K).obj (ring K A))).apply_symm_apply
    (show (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ _ from
      { app := fun U ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U)
        naturality := fun _ _ f ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).naturality
            (F.op.map f) })
  exact congrArg (fun t ↦ t.app U a) h'

omit [RepresentablyFlat F] in
omit [RepresentablyFlat F] in
private def ringMap (A : Type w) [CommRing A] :
    base J A ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj (base K A) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (coefficientMap J K F A)

private theorem restriction_scalar (A : Type w) [CommRing A]
    (M : Modules J A) (U : Cᵒᵖ) (a : A) (x : M.val.obj U) :
    @SMul.smul A (((restriction J A).obj M).obj.obj U) inferInstance a x =
      scalar J A U a • x := by
  change ((constantCommuteCompose J (forget₂ CommRingCat.{w} RingCat.{w})).inv.app
    (CommRingCat.of A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) • x = _
  congr 1
  have hf := congrArg (fun f ↦ f.app U a)
    (sheafComposeIso_hom_fac J (forget₂ CommRingCat.{w} RingCat.{w})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
  have hp := congrArg (fun f ↦ f.app U a) (toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget₂ CommRingCat.{w} RingCat.{w})).hom.app
      (CommRingCat.of A)))
  dsimp at hp
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{w} RingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) _ = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget₂ CommRingCat.{w} RingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) z) hp.symm).trans hf

private def rightComparison (A : Type w) [CommRing A] :
    SheafOfModules.pushforward (ringMap J K F A) ⋙ restriction J A ≅
      restriction K A ⋙ F.sheafPushforwardContinuous (ModuleCat.{w} A) J K := by
  refine NatIso.ofComponents (fun N ↦ {
    hom := { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction J A).obj
          ((SheafOfModules.pushforward (ringMap J K F A)).obj N)).obj.obj U)
        (Y := ((restriction K A).obj N).obj.obj (F.op.obj U)) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
      naturality := by intro U V f; ext x; rfl } }
    inv := { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction K A).obj N).obj.obj (F.op.obj U))
        (Y := ((restriction J A).obj
          ((SheafOfModules.pushforward (ringMap J K F A)).obj N)).obj.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
      naturality := by intro U V f; ext x; rfl } }
    hom_inv_id := by ext U x; rfl
    inv_hom_id := by ext U x; rfl }) (by intro M N f; ext U x; rfl)
  · intro a x
    have hJ := restriction_scalar J A
      ((SheafOfModules.pushforward (ringMap J K F A)).obj N) U a x
    have hK := restriction_scalar K A N (F.op.obj U) a x
    have hφ := congrArg (fun r : (ring K A).obj.obj (F.op.obj U) ↦
      r • (show N.val.obj (F.op.obj U) from x))
      (coefficientMap_scalar J K F A U a)
    exact hJ.trans (hφ.trans hK.symm)
  · intro a x
    have hJ := restriction_scalar J A
      ((SheafOfModules.pushforward (ringMap J K F A)).obj N) U a x
    have hK := restriction_scalar K A N (F.op.obj U) a x
    have hφ := congrArg (fun r : (ring K A).obj.obj (F.op.obj U) ↦
      r • (show N.val.obj (F.op.obj U) from x))
      (coefficientMap_scalar J K F A U a)
    exact hK.trans (hφ.symm.trans hJ.symm)

omit [RepresentablyFlat F] in
end

end CategoryTheory.ConstantScalarRestriction
