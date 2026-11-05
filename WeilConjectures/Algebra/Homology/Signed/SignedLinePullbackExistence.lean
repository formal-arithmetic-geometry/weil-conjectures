/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

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

@[irreducible] private noncomputable def tensorMapBoth
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}]
    {A : Sheaf H CommRingCat.{w}}
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (siteSheafTensorRight N).obj M ⟶ (siteSheafTensorRight N').obj M' :=
  (siteSheafTensorRight N).map f ≫ siteSheafTensorSecondMap M' g

@[irreducible] private noncomputable def overTensorIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M N : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)) :
    ((siteSheafTensorRight N).obj M).over V ≅
      (siteSheafTensorRight (A := A.over V) (N.over V)).obj (M.over V) :=
  (exists_localizedSiteTensorRestriction.{u, v, max u v w, max u v w}
    H A V).choose M N

@[irreducible] private noncomputable def dualIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    {A : Sheaf H CommRingCat.{max u v w}}
    {M N : SheafOfModules.{max u v w}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A)} (e : M ≅ N) :
    homObj M (unit _) ≅ homObj N (unit _) :=
  ((homFunctor A).mapIso e.symm.op).app (unit _)

@[irreducible] private noncomputable def powerOverIso
    {E : Type u} [Category.{v} E] {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify H AddCommGrpCat.{max u v w}]
    (A : Sheaf H CommRingCat.{max u v w}) (V : E)
    [(H.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (H.over V) AddCommGrpCat.{max u v w}]
    (M : SheafOfModules.{max u v w} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj A))
    (e : M.over V ≅ unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V)) :
    ∀ n : ℕ, (scalarTensorPower A M n).over V ≅
      unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V)
  := fun n ↦ Nat.rec (motive := fun n ↦
      (scalarTensorPower A M n).over V ≅
        unit (((sheafCompose H (forget₂ CommRingCat RingCat)).obj A).over V))
    (Iso.refl _) (fun n ih ↦ match n with
      | 0 => e
      | n + 1 => overTensorIso A V (scalarTensorPower A M (n + 1)) M ≪≫
          tensorIso ih e ≪≫ scalarTensorRightUnitor (A.over V) (unit _)) n

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

@[irreducible] private noncomputable def tensorPullbackRaw
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    siteTensorPresheaf M.val N.val ⟶
      ((pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
        ((pullback a).obj M))).val where
  app X := by
    let η := (pullbackPushforwardAdjunction a).unit
    let T := (siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M)
    refine ModuleCat.ofHom (Y := ((pushforward a).obj T).val.obj X)
      (TensorProduct.lift (LinearMap.mk₂ (R.obj.obj X)
      (fun (x : M.val.obj X) (y : N.val.obj X) ↦
        siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N)
        (U.op.obj X) ((η.app M).val.app X x) ((η.app N).val.app X y))
      ?_ ?_ ?_ ?_))
    · intro x y z
      simp only [map_add, scalarTensorTmul_add_first]
    · intro r x y
      have h := ((η.app M).val.app X).hom.map_smul r x
      change (η.app M).val.app X (r • x) =
        (show S.obj.obj (U.op.obj X) from a.hom.app X r) •
          (show ((pullback a).obj M).val.obj (U.op.obj X) from
          (η.app M).val.app X x) at h
      rw [h, scalarTensorTmul_smul_first]
      rfl
    · intro x y z
      simp only [map_add, siteSheafTensorTmul, TensorProduct.tmul_add]
    · intro r x y
      have h := ((η.app N).val.app X).hom.map_smul r y
      change (η.app N).val.app X (r • y) =
        (show S.obj.obj (U.op.obj X) from a.hom.app X r) •
          (show ((pullback a).obj N).val.obj (U.op.obj X) from
          (η.app N).val.app X y) at h
      rw [h, scalarTensorTmul_smul_second]
      rfl
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change siteSheafTensorTmul ((pullback a).obj M) ((pullback a).obj N) (U.op.obj Y)
        (((pullbackPushforwardAdjunction a).unit.app M).val.app Y (M.val.map f x))
        (((pullbackPushforwardAdjunction a).unit.app N).val.app Y (N.val.map f y)) =
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M)).val.map
        (U.op.map f) (siteSheafTensorTmul _ _ (U.op.obj X)
          (((pullbackPushforwardAdjunction a).unit.app M).val.app X x)
          (((pullbackPushforwardAdjunction a).unit.app N).val.app X y))
    rw [scalarTensorTmul_naturality]
    congr 1
    · exact PresheafOfModules.naturality_apply
        ((pullbackPushforwardAdjunction a).unit.app M).val f x
    · exact PresheafOfModules.naturality_apply
        ((pullbackPushforwardAdjunction a).unit.app N).val f y

@[irreducible] private noncomputable def tensorPullback
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (pullback a).obj ((siteSheafTensorRight N).obj M) ⟶
      (siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M) :=
  ((pullbackPushforwardAdjunction a).homEquiv
      ((siteSheafTensorRight N).obj M)
      ((siteSheafTensorRight ((pullback a).obj N)).obj ((pullback a).obj M))).symm
    ((PresheafOfModules.sheafificationHomEquiv
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (R₀ := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) (𝟙 _)
      (P := siteTensorPresheaf M.val N.val)
      (F := (pushforward a).obj ((siteSheafTensorRight ((pullback a).obj N)).obj
        ((pullback a).obj M)))).symm (tensorPullbackRaw a M N))

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
