/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import Submission.WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import Submission.WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses
import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Existence of normalized signed line pullbacks

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-normalized-signed-line-pullback-exists)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

set_option allowUnsafeReducibility true in
attribute [local reducible] siteSheafTensorRight siteTensorRight
  SheafOfModules.forget siteSheafTensorSecondMap
  SheafOfModules.overFunctor PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous Over.forget
  sheafCompose SheafOfModules.unit
  PresheafOfModules.unit SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

attribute [local irreducible] pullback pullbackPushforwardAdjunction
  Functor.leftAdjoint Functor.rightAdjoint

@[irreducible] private noncomputable def tensorIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ≅ M') (g : N ≅ N') :
    (siteSheafTensorRight N).obj M ≅ (siteSheafTensorRight N').obj M' := by
  let raw : siteTensorPresheaf M.val N.val ≅ siteTensorPresheaf M'.val N'.val :=
    { hom := siteTensorHom f.hom.val N.val ≫ siteTensorSecondMap M'.val g.hom.val
      inv := siteTensorHom f.inv.val N'.val ≫ siteTensorSecondMap M.val g.inv.val
      hom_inv_id := by
        ext X : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change f.inv.val.app X (f.hom.val.app X x) ⊗ₜ[A.obj.obj X]
          g.inv.val.app X (g.hom.val.app X y) = x ⊗ₜ[A.obj.obj X] y
        have hf := congrArg (fun t ↦ t.val.app X x) f.hom_inv_id
        have hg := congrArg (fun t ↦ t.val.app X y) g.hom_inv_id
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[A.obj.obj X] b) hf hg
      inv_hom_id := by
        ext X : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change f.hom.val.app X (f.inv.val.app X x) ⊗ₜ[A.obj.obj X]
          g.hom.val.app X (g.inv.val.app X y) = x ⊗ₜ[A.obj.obj X] y
        have hf := congrArg (fun t ↦ t.val.app X x) f.inv_hom_id
        have hg := congrArg (fun t ↦ t.val.app X y) g.inv_hom_id
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[A.obj.obj X] b) hf hg }
  exact (PresheafOfModules.sheafification (𝟙 _)).mapIso raw

private theorem tensorIso_hom
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ≅ M') (g : N ≅ N') :
    (tensorIso f g).hom =
      (siteSheafTensorRight N).map f.hom ≫ siteSheafTensorSecondMap M' g.hom := by
  unfold tensorIso
  exact (PresheafOfModules.sheafification (𝟙 _)).map_comp _ _

section GenericTensorPullback

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]

section TensorPullback

variable {R : Sheaf J CommRingCat.{w}}
  {S : Sheaf K CommRingCat.{w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [hAdjTensor : (pushforward.{w} a).IsRightAdjoint]

set_option allowUnsafeReducibility true in
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  siteSheafTensorRight siteSheafTensorTmul siteSheafTensorSecondMap

end TensorPullback
end GenericTensorPullback

set_option allowUnsafeReducibility true in
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  siteSheafTensorRight siteSheafTensorTmul siteSheafTensorSecondMap

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

section TensorPullback

variable {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [(pushforward.{max u v w} a).IsRightAdjoint]

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] RingedSitePullback.localComparison
set_option allowUnsafeReducibility true in
attribute [local semireducible] sheafCompose siteTensorRight SheafOfModules.forget
  SheafOfModules.unit PresheafOfModules.unit Functor.sheafPushforwardContinuous
  Over.forget SheafOfModules.overFunctor
  PresheafOfModules.restrictOver SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

end TensorPullback

end SheafOfModules
