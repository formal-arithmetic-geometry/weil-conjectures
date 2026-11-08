/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Internal Hom of constant module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(blueprint: lem-pur-site-constant-module-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
private instance homUnit_surjective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance homUnit_injective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private lemma homUnit_naturality {M N : ModuleCat.{max u v} Λ} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((constantModuleHomFunctor J Λ).map f).val.app U
      ((constantModuleHomUnit J Λ M).app U x) =
        (constantModuleHomUnit J Λ N).app U (f x) := by
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) Λ).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

private def homMap (M N : ModuleCat.{max u v} Λ) (f : M →ₗ[Λ] N) :
    (constantModuleHomFunctor J Λ).obj M ⟶ (constantModuleHomFunctor J Λ).obj N :=
  (constantModuleHomFunctor J Λ).map (show M ⟶ N from ModuleCat.ofHom f)

private lemma homMap_unit (M N : ModuleCat.{max u v} Λ) (f : M →ₗ[Λ] N)
    (U : Cᵒᵖ) (x : M) :
    (homMap J Λ M N f).val.app U ((constantModuleHomUnit J Λ M).app U x) =
      (constantModuleHomUnit J Λ N).app U (f x) :=
  homUnit_naturality J Λ (show M ⟶ N from ModuleCat.ofHom f) U x

private abbrev homCommRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)

private abbrev homRing :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    (homCommRing J Λ)

private def homRingUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ (homRing J Λ).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) ≫
    (constantModuleHomRingIso J Λ).hom.hom

set_option backward.isDefEq.respectTransparency false in
private def homUnitLinear (M : ModuleCat.{max u v} Λ) :
    (siteConstantModulePresheafGeneral (C := C) Λ).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
        ((constantModuleHomFunctor J Λ).obj M).val :=
  PresheafOfModules.homMk (constantModuleHomUnit J Λ M) (fun U r x ↦ by
    have hi := congrArg
      (fun f ↦ f.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r))
      (constantModuleHomRingIso J Λ).hom_inv_id
    change (constantModuleHomRingIso J Λ).inv.hom.app U
      ((constantModuleHomRingIso J Λ).hom.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r at hi
    change (constantModuleHomUnit J Λ M).app U (r • x) =
      (constantModuleHomRingIso J Λ).inv.hom.app U
        ((constantModuleHomRingIso J Λ).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r)) •
        (show ((siteConstantModuleFunctorGeneral J Λ).obj M).val.obj U from
          (constantModuleHomUnit J Λ M).app U x)
    rw [hi]
    exact (((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)).app U).hom.map_smul r x)

private lemma homUnit_ext (M N : ModuleCat.{max u v} Λ) (U : C)
    (a b : (PresheafOfModules.restrictOver (homCommRing J Λ).obj U).obj
        ((constantModuleHomFunctor J Λ).obj M).val ⟶
      (PresheafOfModules.restrictOver (homCommRing J Λ).obj U).obj
        ((constantModuleHomFunctor J Λ).obj N).val)
    (h : ∀ (V : Over U) (x : M),
      a.app (op V) ((constantModuleHomUnit J Λ M).app (op V.left) x) =
        b.app (op V) ((constantModuleHomUnit J Λ M).app (op V.left) x)) : a = b := by
  let FM := (constantModuleHomFunctor J Λ).obj M
  let FN := (constantModuleHomFunctor J Λ).obj N
  let η := constantModuleHomUnit J Λ M
  ext V s
  apply FN.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U := Over.mk (f ≫ V.unop.hom)
  have ha := PresheafOfModules.naturality_apply a
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := PresheafOfModules.naturality_apply b
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.app (op V') (FM.val.map f.op s) = FN.val.map f.op (a.app V s) at ha
  change b.app (op V') (FM.val.map f.op s) = FN.val.map f.op (b.app V s) at hb
  change η.app (op W) x = FM.val.map f.op s at hx
  change FN.val.map f.op (a.app V s) = FN.val.map f.op (b.app V s)
  rw [← ha, ← hb, ← hx]
  exact h V' x

set_option backward.isDefEq.respectTransparency false in
private def homConstMap (M N : ModuleCat.{max u v} Λ) :
    (siteConstantModulePresheafGeneral (C := C) Λ).obj
        (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
        (SheafOfModules.homObj (R := homCommRing J Λ)
          ((constantModuleHomFunctor J Λ).obj M)
          ((constantModuleHomFunctor J Λ).obj N)).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).val).obj U)
    { toFun f := (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
        ((homMap J Λ M N f).val)
      map_add' f g := by
        apply homUnit_ext J Λ M N U.unop
        intro V x
        change (homMap J Λ M N (f + g)).val.app _
            ((constantModuleHomUnit J Λ M).app _ x) =
          (homMap J Λ M N f).val.app _
              ((constantModuleHomUnit J Λ M).app _ x) +
            (homMap J Λ M N g).val.app _
              ((constantModuleHomUnit J Λ M).app _ x)
        erw [homMap_unit J Λ M N,
          homMap_unit J Λ M N,
          homMap_unit J Λ M N]
        exact ((constantModuleHomUnit J Λ N).app (op V.left)).hom.map_add (f x) (g x)
      map_smul' r f := by
        change (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
            ((homMap J Λ M N (r • f)).val) =
          (show (homCommRing J Λ).obj.obj (op U.unop) from (homRingUnit J Λ).app U r) •
            (PresheafOfModules.restrictOver (homCommRing J Λ).obj U.unop).map
              ((homMap J Λ M N f).val)
        apply homUnit_ext J Λ M N U.unop
        intro V x
        change (homMap J Λ M N (r • f)).val.app _
            ((constantModuleHomUnit J Λ M).app _ x) =
          (homRing J Λ).obj.map V.hom.op ((homRingUnit J Λ).app U r) •
            (show ((constantModuleHomFunctor J Λ).obj N).val.obj (op V.left) from
              (homMap J Λ M N f).val.app _
                ((constantModuleHomUnit J Λ M).app _ x))
        erw [homMap_unit J Λ M N,
          homMap_unit J Λ M N]
        have hn := NatTrans.naturality_apply (homRingUnit J Λ) V.hom.op r
        change (homRingUnit J Λ).app (op V.left) r =
          (homRing J Λ).obj.map V.hom.op ((homRingUnit J Λ).app U r) at hn
        rw [← hn]
        exact ((homUnitLinear J Λ N).app (op V.left)).hom.map_smul r (f x) }
  naturality {U V} g := by
    ext f
    rfl

private instance homRingUnit_surjective : Presheaf.IsLocallySurjective J (homRingUnit J Λ) := by
  unfold homRingUnit
  infer_instance

private instance homUnitLinear_surjective (M : ModuleCat.{max u v} Λ) :
    PresheafOfModules.IsLocallySurjective J (homUnitLinear J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance homUnitLinear_injective (M : ModuleCat.{max u v} Λ) :
    PresheafOfModules.IsLocallyInjective J (homUnitLinear J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private def homComparison (M N : ModuleCat.{max u v} Λ) :
    (constantModuleHomFunctor J Λ).obj (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
      SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M) ((constantModuleHomFunctor J Λ).obj N) where
  val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective (homRingUnit J Λ)
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).isSheaf).symm
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (homUnitLinear J Λ (ModuleCat.of Λ (M →ₗ[Λ] N)))
      (SheafOfModules.homObj (R := homCommRing J Λ)
        ((constantModuleHomFunctor J Λ).obj M)
        ((constantModuleHomFunctor J Λ).obj N)).isSheaf).symm (homConstMap J Λ M N))

private def homSections (M : ModuleCat.{max u v} Λ) : Cᵒᵖ ⥤ ModuleCat.{max u v} Λ where
  obj U := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
    ((constantModuleHomFunctor J Λ).obj M).val).obj U
  map f := ((PresheafOfModules.restrictScalars (homRingUnit J Λ)).obj
    ((constantModuleHomFunctor J Λ).obj M).val).map f
  map_id U := by ext x; simp; rfl
  map_comp f g := by ext x; simp; rfl

private def homSectionsUnit (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶ homSections J Λ M where
  app U := (homUnitLinear J Λ M).app U
  naturality {U V} f := by
    ext x
    exact NatTrans.naturality_apply (constantModuleHomUnit J Λ M) f x

private instance homSectionsUnit_injective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (homSectionsUnit J Λ M) where
  equalizerSieve_mem x y h :=
    Presheaf.equalizerSieve_mem J (constantModuleHomUnit J Λ M) x y h

private instance homSectionsUnit_surjective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (homSectionsUnit J Λ M) where
  imageSieve_mem x := Presheaf.imageSieve_mem J (constantModuleHomUnit J Λ M) x

end CategoryTheory
