/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
import Sheaf.Algebra.Homology.SliceModuleSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Lifting.Left
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Sheaf.CategoryTheory.FiniteTypeRestrictionExact

/-! # The canonical module comparison for localization of a ringed site

Source: Stacks Project, Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-module-pullback-isIso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace CategoryTheory
section ChangeLeft
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂)
  {G : C ⥤ E} {H : D ⥤ F} (b : TwoSquare R₁ H G R₂)
private theorem changeLeftMate (X : C) :
    ((mateEquiv a₁ a₂).symm b).app X =
      (a₂.leftAdjointUniq a₂').hom.app (G.obj X) ≫
        ((mateEquiv a₁' a₂').symm b).app X ≫
          H.map ((a₁.leftAdjointUniq a₁').inv.app X) := by
  apply (a₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [a₂.unit_leftAdjointUniq_hom_app a₂']
  have h := unit_mateEquiv_symm a₁' a₂' b X
  change G.map (a₁'.unit.app X) ≫ b.app (L₁'.obj X) =
    a₂'.unit.app (G.obj X) ≫ R₂.map (((mateEquiv a₁' a₂').symm b).app X) at h
  rw [← h]
  have hn := b.natTrans.naturality ((a₁.leftAdjointUniq a₁').inv.app X)
  change G.map (R₁.map ((a₁.leftAdjointUniq a₁').inv.app X)) ≫ b.app (L₁.obj X) =
    b.app (L₁'.obj X) ≫ R₂.map (H.map ((a₁.leftAdjointUniq a₁').inv.app X)) at hn
  rw [Category.assoc, ← hn, ← G.map_comp_assoc]
  have hi : a₁'.unit.app X ≫ R₁.map ((a₁.leftAdjointUniq a₁').inv.app X) =
      a₁.unit.app X := by
    rw [a₁.leftAdjointUniq_inv_app a₁']
    exact a₁'.unit_leftAdjointUniq_hom_app a₁ X
  rw [hi]
  exact (unit_mateEquiv_symm a₁ a₂ b X).symm

private theorem changeLeftMate_isIso
    [IsIso ((mateEquiv a₁' a₂').symm b).natTrans] :
    IsIso ((mateEquiv a₁ a₂).symm b).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  change IsIso (((mateEquiv a₁ a₂).symm b).app X)
  rw [changeLeftMate a₁ a₁' a₂ a₂']
  infer_instance
end ChangeLeft

section FreePresentation
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Abelian D]
  {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) [U.Faithful]
  {L L' : D ⥤ E} (t : L ⟶ L') [PreservesColimitsOfShape WalkingParallelPair L]
  [PreservesColimitsOfShape WalkingParallelPair L']
  (h : ∀ X : C, IsIso (t.app (F.obj X)))
include adj h in
private theorem freePresentation_isIso : IsIso t := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let r : ∀ Y : D, RegularEpi (adj.counit.app Y) := fun Y ↦
    { W := kernel (adj.counit.app Y)
      left := kernel.ι _
      right := 0
      w := by simp
      isColimit := Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (adj.counit.app Y)) (kernel.condition _))
        (kernelIsKernel _) }
  let c := Cofork.ofπ (adj.counit.app X) (adj.counit_naturality _)
  have hc : IsColimit c := LiftLeftAdjoint.counitCoequalises adj r X
  let ht : IsIso (Functor.whiskerLeft (parallelPair
    (F.map (U.map (adj.counit.app X))) (adj.counit.app (F.obj (U.obj X)))) t) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    cases j <;> exact h _
  exact @isIso_app_coconePt_of_preservesColimit _ _ _ _ _ _ _ _ _ t ht c hc _ _
end FreePresentation
end CategoryTheory

namespace SheafOfModules
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
private abbrev sets (R : Sheaf J RingCat.{u}) :=
  toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
private abbrev freeP (R : Sheaf J RingCat.{u}) :=
  PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
private abbrev freeS (R : Sheaf J RingCat.{u}) :=
  sheafToPresheaf J (Type u) ⋙ freeP R
private def freePAdj (R : Sheaf J RingCat.{u}) :
    freeP R ⊣ sets R ⋙ sheafToPresheaf J (Type u) :=
  ((PresheafOfModules.freeAdjunction R.obj).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private def freeAdj (R : Sheaf J RingCat.{u}) : freeS R ⊣ sets R :=
  (freePAdj R).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J (Type u))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

private def freeRestrictionIso (R : Sheaf J RingCat.{u}) (V : C) :
    J.overPullback (Type u) V ⋙ freeS (R.over V) ≅
      freeS R ⋙ overFunctor R V :=
  haveI := sliceSheafificationComparison_isIso (J := J.over V) (Over.forget V) R
  NatIso.ofComponents (fun A ↦
    asIso ((sliceSheafificationComparison (J := J.over V) (Over.forget V) R).app
      ((PresheafOfModules.free R.obj).obj A.obj))) (by
    intro A B f
    exact (sliceSheafificationComparison (J := J.over V) (Over.forget V) R).naturality
      ((PresheafOfModules.free R.obj).map f.hom))

private theorem freeRestriction_unit (R : Sheaf J RingCat.{u}) (V : C)
    (A : Sheaf J (Type u)) :
    ((freeAdj (R.over V)).homEquiv _ _ ((freeRestrictionIso R V).hom.app A)) =
      (J.overPullback (Type u) V).map ((freeAdj R).unit.app A) := by
  apply (fullyFaithfulSheafToPresheaf (J.over V) (Type u)).map_injective
  ext T x
  change ((freeRestrictionIso R V).hom.app A).val.app T
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (R.over V).obj)).unit.app
      ((PresheafOfModules.free (R.over V).obj).obj (A.over V).obj)).app T
        (ModuleCat.freeMk x)) = _
  have h := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (R.over V).obj)).homEquiv
        ((PresheafOfModules.free (R.over V).obj).obj (A.over V).obj)
        ((overFunctor R V).obj ((freeS R).obj A))).apply_symm_apply
    ((slicePresheafRestriction (J := J.over V) (Over.forget V) R).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
        ((PresheafOfModules.free R.obj).obj A.obj)))
  change ((freeRestrictionIso R V).hom.app A).val.app T
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (R.over V).obj)).unit.app
      ((PresheafOfModules.free (R.over V).obj).obj (A.over V).obj)).app T
        (ModuleCat.freeMk x)) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
      ((PresheafOfModules.free R.obj).obj A.obj)).app (op T.unop.left)
        (ModuleCat.freeMk x)
  exact congrArg (fun g ↦ g.app T (ModuleCat.freeMk x)) h

end SheafOfModules

namespace SheafOfModules
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous RingCat.{u} K J).obj S)

/-- Restrict the coefficient map sectionwise. Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
def sliceModuleRingMap (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))] :
    R.over V ⟶ ((Over.post (X := V) u).sheafPushforwardContinuous RingCat.{u}
      (K.over V) (J.over (u.obj V))).obj (S.over (u.obj V)) :=
  ⟨{ app T := a.hom.app (op T.unop.left)
     naturality _T _T' f := a.hom.naturality ((Over.forget V).op.map f) }⟩

/-- The direct-image square is identity on sections. Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
def sliceModulePushforwardIso (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))] :
    pushforward a ⋙
        overFunctor R V ≅
      overFunctor S (u.obj V) ⋙
        pushforward (sliceModuleRingMap u a V) :=
  NatIso.ofComponents (fun G ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun T ↦ Iso.refl _)))

/-- The canonical inverse mate of the sectionwise identity. Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
def sliceModulePullbackMap (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))] :
    overFunctor R V ⋙
        pullback (sliceModuleRingMap u a V) ⟶
      pullback a ⋙
        overFunctor S (u.obj V) :=
  ((mateEquiv (pullbackPushforwardAdjunction a)
    (pullbackPushforwardAdjunction (sliceModuleRingMap u a V))).symm
        (TwoSquare.mk _ _ _ _ (sliceModulePushforwardIso u a V).hom)).natTrans

/-- The unit equation characterizes the canonical module inverse mate.
Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
theorem sliceModulePullbackMap_unit (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (A : SheafOfModules.{u} R) :
    (overFunctor R V).map ((pullbackPushforwardAdjunction a).unit.app A) ≫
        (sliceModulePushforwardIso u a V).hom.app ((pullback a).obj A) =
      (pullbackPushforwardAdjunction (sliceModuleRingMap u a V)).unit.app
          ((overFunctor R V).obj A) ≫
        (pushforward (sliceModuleRingMap u a V)).map
          ((sliceModulePullbackMap u a V).app A) := by
  exact unit_mateEquiv_symm (pullbackPushforwardAdjunction a)
    (pullbackPushforwardAdjunction (sliceModuleRingMap u a V))
    (TwoSquare.mk _ _ _ _ (sliceModulePushforwardIso u a V).hom) A

/-- A module comparison satisfying the canonical unit equation is the inverse mate.
Source: Stacks Tag 04J0, uniqueness under the module adjunction
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
theorem sliceModulePullbackMap_eq_of_unit (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (t : overFunctor R V ⋙ pullback (sliceModuleRingMap u a V) ⟶
      pullback a ⋙ overFunctor S (u.obj V))
    (ht : ∀ A : SheafOfModules.{u} R,
      (pullbackPushforwardAdjunction (sliceModuleRingMap u a V)).unit.app
          ((overFunctor R V).obj A) ≫
        (pushforward (sliceModuleRingMap u a V)).map (t.app A) =
      (overFunctor R V).map ((pullbackPushforwardAdjunction a).unit.app A) ≫
        (sliceModulePushforwardIso u a V).hom.app ((pullback a).obj A)) :
    t = sliceModulePullbackMap u a V := by
  apply NatTrans.ext
  funext A
  apply ((pullbackPushforwardAdjunction (sliceModuleRingMap u a V)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ht]
  exact sliceModulePullbackMap_unit u a V A

/-- The inverse mate commutes with taking adjuncts. Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-slice-module-pullback-isIso). -/
theorem sliceModulePullbackMap_adjunct (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (A : SheafOfModules.{u} R)
    (B : SheafOfModules.{u} S)
    (h : A ⟶ (pushforward a).obj B) :
    (sliceModulePullbackMap u a V).app A ≫
        (overFunctor S (u.obj V)).map
          (((pullbackPushforwardAdjunction a).homEquiv A B).symm h) =
      ((pullbackPushforwardAdjunction (sliceModuleRingMap u a V)).homEquiv _ _).symm
        ((overFunctor R V).map h ≫
          (sliceModulePushforwardIso u a V).hom.app B) := by
  let adj := pullbackPushforwardAdjunction a
  let adjV := pullbackPushforwardAdjunction (sliceModuleRingMap u a V)
  let jV := overFunctor R V
  let jU := overFunctor S (u.obj V)
  let b := sliceModulePushforwardIso u a V
  let l := sliceModulePullbackMap u a V
  have hl := sliceModulePullbackMap_unit (K := K) (J := J) u a V A
  apply (adjV.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change adjV.unit.app (jV.obj A) ≫
      (pushforward (sliceModuleRingMap u a V)).map
        (l.app A ≫ jU.map ((adj.homEquiv A B).symm h)) = _
  change jV.map (adj.unit.app A) ≫ b.hom.app _ =
    adjV.unit.app (jV.obj A) ≫
      (pushforward (sliceModuleRingMap u a V)).map (l.app A) at hl
  rw [Functor.map_comp, ← Category.assoc, ← hl]
  have hn := b.hom.naturality ((adj.homEquiv A B).symm h)
  change jV.map ((pushforward a).map
      ((adj.homEquiv A B).symm h)) ≫ b.hom.app B =
    b.hom.app _ ≫ (pushforward (sliceModuleRingMap u a V)).map
        (jU.map ((adj.homEquiv A B).symm h)) at hn
  rw [Category.assoc, ← hn]
  change jV.map (adj.unit.app A) ≫
      jV.map ((pushforward a).map ((adj.homEquiv A B).symm h)) ≫
        b.hom.app B = _
  rw [← jV.map_comp_assoc]
  have ha := (adj.homEquiv A B).apply_symm_apply h
  rw [Adjunction.homEquiv_unit] at ha
  change adj.unit.app A ≫
    (pushforward a).map ((adj.homEquiv A B).symm h) = h at ha
  exact congrArg (fun k ↦ jV.map k ≫ b.hom.app B) ha

private def freeRestrictionRight (R : Sheaf K RingCat.{u}) (V : D) :
    TwoSquare (sets R) (overFunctor R V) (K.overPullback (Type u) V) (sets (R.over V)) :=
  { app _ := 𝟙 _
    naturality _ _ f := by rfl }

private def freeRestrictionMate (R : Sheaf K RingCat.{u}) (V : D) :
    TwoSquare (K.overPullback (Type u) V) (freeS R) (freeS (R.over V))
      (overFunctor R V) :=
  (mateEquiv (freeAdj R) (freeAdj (R.over V))).symm (freeRestrictionRight R V)

private theorem freeRestrictionMate_eq (R : Sheaf K RingCat.{u}) (V : D) :
    (freeRestrictionMate R V).natTrans = (freeRestrictionIso R V).hom := by
  apply NatTrans.ext
  funext A
  apply ((freeAdj (R.over V)).homEquiv _ _).injective
  rw [freeRestriction_unit, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (freeAdj R) (freeAdj (R.over V))
    (freeRestrictionRight R V) A).symm.trans (by simp [freeRestrictionRight])

private theorem freeRestrictionMate_isIso (R : Sheaf K RingCat.{u}) (V : D) :
    IsIso (freeRestrictionMate R V).natTrans := by
  rw [freeRestrictionMate_eq]
  infer_instance

private theorem moduleFreeComparison_isIso (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    (A : Sheaf K (Type u)) :
    IsIso ((sliceModulePullbackMap u a V).app ((freeS R).obj A)) := by
  let af := freeAdj R
  let afV := freeAdj (R.over V)
  let ag := freeAdj S
  let agV := freeAdj (S.over (u.obj V))
  let am := pullbackPushforwardAdjunction a
  let amV := pullbackPushforwardAdjunction (sliceModuleRingMap u a V)
  let az := u.sheafAdjunctionContinuous (Type u) K J
  let azV := (Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
    (K.over V) (J.over (u.obj V))
  let b : TwoSquare (pushforward a ⋙ sets R) (overFunctor S (u.obj V))
      (K.overPullback (Type u) V)
      (pushforward (sliceModuleRingMap u a V) ⋙ sets (R.over V)) :=
    { app _ := 𝟙 _
      naturality _ _ f := by rfl }
  let bₘ := TwoSquare.mk _ _ _ _ (sliceModulePushforwardIso u a V).hom
  let bₛ := TwoSquare.mk _ _ _ _ (sliceSetPushforwardIso (K := K) (J := J) u V).hom
  let α := freeRestrictionMate R V
  let β := (mateEquiv am amV).symm bₘ
  let γ := (mateEquiv az azV).symm bₛ
  let δ := freeRestrictionMate S (u.obj V)
  have ha : ((mateEquiv (af.comp am) (afV.comp amV)).symm b) = α ≫ᵥ β := by
    apply (mateEquiv (af.comp am) (afV.comp amV)).injective
    rw [Equiv.apply_symm_apply, mateEquiv_hcomp]
    change b =
      (mateEquiv am amV ((mateEquiv am amV).symm bₘ)) ≫ₕ
        (mateEquiv af afV ((mateEquiv af afV).symm (freeRestrictionRight R V)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext M T x
    rfl
  have hb : ((mateEquiv (az.comp ag) (azV.comp agV)).symm b) = γ ≫ᵥ δ := by
    apply (mateEquiv (az.comp ag) (azV.comp agV)).injective
    rw [Equiv.apply_symm_apply, mateEquiv_hcomp]
    change b =
      (mateEquiv ag agV ((mateEquiv ag agV).symm (freeRestrictionRight S (u.obj V)))) ≫ₕ
        (mateEquiv az azV ((mateEquiv az azV).symm bₛ))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext M T x
    rfl
  have hγ : IsIso γ.natTrans := sliceSetPullbackMap_isIso (K := K) (J := J) u V
  have hδ : IsIso δ.natTrans := freeRestrictionMate_isIso S (u.obj V)
  have hnew : IsIso (((mateEquiv (az.comp ag) (azV.comp agV)).symm b).natTrans) := by
    rw [hb]
    dsimp only [TwoSquare.vComp]
    infer_instance
  have hh := changeLeftMate_isIso (af.comp am) (az.comp ag)
    (afV.comp amV) (azV.comp agV) b
  rw [ha] at hh
  have hα : IsIso α.natTrans := freeRestrictionMate_isIso R V
  have hcomp : IsIso ((pullback (sliceModuleRingMap u a V)).map (α.app A) ≫
      (sliceModulePullbackMap u a V).app ((freeS R).obj A)) := by
    have hi : IsIso ((α ≫ᵥ β).natTrans.app A) := inferInstance
    simpa only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id, β, bₘ, sliceModulePullbackMap] using hi
  exact IsIso.of_isIso_comp_left
    ((pullback (sliceModuleRingMap u a V)).map (α.app A)) _

/-- The canonical module inverse mate for a geometric morphism is invertible.
Source: Stacks Project, Modules on Sites, Tag 04J0, proof; Sites, Tag 03CF.
(blueprint: lem-weil-pbc-slice-module-pullback-isIso).

Proof: Identify slice sheaves with objects over the sheafified representable.
The geometric inverse image takes the representable of V to that of u(V), and
preserves the products computing restriction, giving the canonical set inverse mate.
Construct the free-sheaf-module adjunction by sheafifying presheaf free modules.
Restriction commutes with free modules sectionwise and with sheafification by
continuous cocontinuous restriction. The sheafification unit equation identifies
this isomorphism with the free-module restriction inverse mate. Paste mates for
free modules and module pullback; uniqueness of left adjoints identifies this
with the pasted set and free-module comparison. Cancellation proves the desired
comparison invertible on free modules. The faithful underlying-set functor makes
the free-module counit a regular epimorphism. Its canonical coequalizer presents
every module by free modules. Pullback and restriction preserve this coequalizer,
so invertibility on the free terms proves invertibility on every module.
This also covers the zero ring and empty covering sieves. -/
theorem sliceModulePullbackMap_isIso
    {R' : Sheaf K CommRingCat.{u}} {S' : Sheaf J CommRingCat.{u}}
    (a' : R' ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S')
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))] :
    IsIso (sliceModulePullbackMap (K := K) (J := J) u
      (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S')
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map a') V) := by
  let := (overFunctor_exact ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R') V).2
  let := (overFunctor_exact ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S')
    (u.obj V)).2
  exact freePresentation_isIso
    (freeAdj ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (sliceModulePullbackMap u
      (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S')
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map a') V)
    (moduleFreeComparison_isIso u _ V)

end SheafOfModules

