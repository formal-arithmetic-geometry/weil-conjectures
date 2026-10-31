/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-!
# Monoidal pullback and restriction along a pro-etale object

Source: Stacks Project, Pro-etale Cohomology, Tag 098T; Sites and Sheaves,
Tags 00Y0 and 03EH; Modules on Sites, Section 03DH
(blueprint: lem-sfb-proetale-object-pullback-restriction).

All restrictions below are the existing sectionwise pushforward along composition
of site objects. Its lax maps are those induced by objectwise tensor followed by
sheafification. The pullback comparison is the existing canonical adjunction comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pullback along a site object is sectionwise restriction, monoidally, and the
canonical restriction tensor and unit maps are invertible.
Source: Stacks Tags 098T and 00Y0
(blueprint: lem-sfb-proetale-object-pullback-restriction).

Proof: the distinguished initial Kan index identifies the sheafified left Kan
extension with restriction. Under this identification its adjunction unit at T is
restriction along T ×_Y W → T. The oplax tensor map is the mate of the pushforward
lax tensor map after the two units. Both sides of the monoidal comparison equation
send a pure tensor a ⊗ b to the sheafification image of the restricted a ⊗ b.
These tensors generate the presheaf tensor, and maps out of sheafification are
uniquely determined there. The unit calculation sends 1 to 1. The mate bijection
therefore gives both monoidal equations. Restriction commutes with sheafification
on the localized site and with objectwise tensor, so its comparison maps are
invertible. Finally composition of site objects gives the displayed section formula,
including at the final object W → W.
-/
theorem proEtaleObjectPullbackRestriction (Y : Scheme.{u}) (W : Y.ProEt) :
    NatTrans.IsMonoidal (upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop).hom ∧
    IsIso (Functor.LaxMonoidal.ε
      (@Functor.sheafPushforwardContinuous W.left.ProEt _ Y.ProEt _
        (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop) Ab.{u + 1} _
        (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.isContinuous_overMap W.prop))) ∧
    (∀ F G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1},
      IsIso (Functor.LaxMonoidal.μ
        (@Functor.sheafPushforwardContinuous W.left.ProEt _ Y.ProEt _
          (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop) Ab.{u + 1} _
          (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.isContinuous_overMap W.prop)) F G)) ∧
    (∀ (F : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (V : W.left.ProEt),
      ((localizationRestriction Ab.{u + 1} W.hom W.prop).obj F).obj.obj (op V) =
        F.obj.obj (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj V))) := by
  let e := upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop
  refine ⟨inferInstance, ?_, ?_, fun _ _ ↦ rfl⟩
  · have hi : IsIso (Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} W.hom) ≫
        e.hom.app (𝟙_ _)) := inferInstance
    exact (NatTrans.IsMonoidal.unit (τ := e.hom)) ▸ hi
  · intro F G
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) F G
    have hi : IsIso ((e.hom.app F ⊗ₘ e.hom.app G) ≫
        Functor.LaxMonoidal.μ _ F G) := by
      rw [← h]
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (e.hom.app F ⊗ₘ e.hom.app G) _ inferInstance hi

private abbrev restrictionSiteFunctor (Y : Scheme.{u}) (W : Y.ProEt) :=
  MorphismProperty.Over.map (f := W.hom) ⊤ W.prop

private instance restrictionSiteFunctor_continuous (Y : Scheme.{u}) (W : Y.ProEt) :
    (restrictionSiteFunctor Y W).IsContinuous
      (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y) :=
  Scheme.ProEt.isContinuous_overMap W.prop

private instance restrictionSiteFunctor_cocontinuous (Y : Scheme.{u}) (W : Y.ProEt) :
    (restrictionSiteFunctor Y W).IsCocontinuous
      (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y) :=
  Scheme.ProEt.isCocontinuous_overMap W.prop

private def restrictionRingIso (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] :
    (constantSheaf (Scheme.ProEt.topology W.left) RingCat.{u + 1}).obj (RingCat.of B) ≅
      ((restrictionSiteFunctor Y W).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)).obj
          ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj (RingCat.of B)) :=
  ((restrictionSiteFunctor Y W).pushforwardContinuousSheafificationCompatibility
    RingCat.{u + 1} (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)).app
      ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))

private theorem restrictionRingIso_unit (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (V : W.left.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B))).app V ≫
      (restrictionRingIso Y W B).hom.hom.app V =
    (toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))).app
      ((restrictionSiteFunctor Y W).op.obj V) :=
  congr_app ((restrictionSiteFunctor Y W).toSheafify_pullbackSheafificationCompatibility
    RingCat.{u + 1} (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))) V

private def restrictionConstantSeed (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (P : ModuleCat.{u + 1} B) :
    (siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj P ⟶
      (PresheafOfModules.restrictScalars
        (toSheafify (Scheme.ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B)))).obj
        ((SheafOfModules.pushforward (F := restrictionSiteFunctor Y W)
          (restrictionRingIso Y W B).hom).obj
            ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj P)).val := by
  let t := PresheafOfModules.toSheafify
    (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B)))
    (toSheafify (Scheme.ProEt.topology Y)
      ((siteConstantModulePresheafGeneral (C := Y.ProEt) B).obj P).presheaf)
  refine PresheafOfModules.homMk
    (Functor.whiskerLeft (restrictionSiteFunctor Y W).op
      (toSheafify (Scheme.ProEt.topology Y)
        ((siteConstantModulePresheafGeneral (C := Y.ProEt) B).obj P).presheaf)) ?_
  intro V b p
  refine ((t.app ((restrictionSiteFunctor Y W).op.obj V)).hom.map_smul b p).trans ?_
  have hb := ConcreteCategory.congr_hom (restrictionRingIso_unit Y W B V) b
  exact congrArg
    (fun b' : ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of B)).obj.obj ((restrictionSiteFunctor Y W).op.obj V) ↦
      b' • (show ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj P).val.obj
        ((restrictionSiteFunctor Y W).op.obj V) from
          t.app ((restrictionSiteFunctor Y W).op.obj V) p)) hb.symm

private def restrictionConstantComparison (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (P : ModuleCat.{u + 1} B) :
    (siteConstantModuleFunctorGeneral (Scheme.ProEt.topology W.left) B).obj P ⟶
      (SheafOfModules.pushforward (F := restrictionSiteFunctor Y W)
        (restrictionRingIso Y W B).hom).obj
          ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify (Scheme.ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B)))).symm
        (restrictionConstantSeed Y W B P)

private theorem restrictionConstantComparison_fac (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (P : ModuleCat.{u + 1} B) :
    toSheafify (Scheme.ProEt.topology W.left)
        ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj P).presheaf ≫
      ((SheafOfModules.toSheaf _).map (restrictionConstantComparison Y W B P)).hom =
    Functor.whiskerLeft (restrictionSiteFunctor Y W).op
      (toSheafify (Scheme.ProEt.topology Y)
        ((siteConstantModulePresheafGeneral (C := Y.ProEt) B).obj P).presheaf) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (toSheafify (Scheme.ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B)))
    (restrictionConstantComparison Y W B P)
  dsimp only [restrictionConstantComparison] at h
  rw [Equiv.apply_symm_apply] at h
  calc
    _ = (PresheafOfModules.toPresheaf _).map (restrictionConstantSeed Y W B P) := h.symm
    _ = _ := by
      ext V p
      rfl

private instance restrictionConstantComparison_isIso (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (P : ModuleCat.{u + 1} B) :
    IsIso (restrictionConstantComparison Y W B P) := by
  have h : (SheafOfModules.toSheaf _).map (restrictionConstantComparison Y W B P) =
      ((restrictionSiteFunctor Y W).pushforwardContinuousSheafificationCompatibility
        Ab.{u + 1} (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)).hom.app
          ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of P)) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Scheme.ProEt.topology W.left) _ _
      (((restrictionSiteFunctor Y W).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)).obj
          ((constantSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).obj (AddCommGrpCat.of P))).property
    exact (restrictionConstantComparison_fac Y W B P).trans
      ((restrictionSiteFunctor Y W).toSheafify_pullbackSheafificationCompatibility
        Ab.{u + 1} (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of P))).symm
  have : IsIso ((SheafOfModules.toSheaf _).map
      (restrictionConstantComparison Y W B P)) := by
    rw [h]
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- Constant rings and constant modules restrict canonically to the corresponding
constant ring and module on W. Both comparisons preserve the constant sections.
Source: Stacks Tag 00Y0 and Modules on Sites, Section 03DH
(blueprint: lem-sfb-proetale-object-pullback-restriction).

Proof: restricting the constant presheaf gives the same constant presheaf. The
slice-sheafification comparison gives the ring isomorphism, identity on constants,
and the analogous abelian-group isomorphism for each module P. The latter is linear:
the two maps expressing linearity agree on constant pairs (b,p), where both give bp;
the sheafification universal property extends this equality to all sections. It is
natural on linear maps by the same uniqueness. Evaluation at the final object of
W_proet is evaluation at W → Y after composition, with the same sections and action.
-/
theorem proEtaleObjectConstantModuleRestriction (Y : Scheme.{u}) (W : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] :
    ∃ e : (constantSheaf (Scheme.ProEt.topology W.left) RingCat.{u + 1}).obj
          (RingCat.of B) ≅
        (@Functor.sheafPushforwardContinuous W.left.ProEt _ Y.ProEt _
          (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop) RingCat.{u + 1} _
          (Scheme.ProEt.topology W.left) (Scheme.ProEt.topology Y)
          (Scheme.ProEt.isContinuous_overMap W.prop)).obj
            ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj (RingCat.of B)),
      (∀ V : W.left.ProEt,
        (toSheafify (Scheme.ProEt.topology W.left)
            ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B))).app (op V) ≫
            e.hom.hom.app (op V) =
          (toSheafify (Scheme.ProEt.topology Y)
            ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj V))) ∧
      ∃ c : siteConstantModuleFunctorGeneral (Scheme.ProEt.topology W.left) B ≅
          siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B ⋙
            @SheafOfModules.pushforward.{u + 1} _ _ _ _ _ _ _ _ _
              (Scheme.ProEt.isContinuous_overMap W.prop) e.hom,
        ∀ (P : ModuleCat.{u + 1} B) (V : W.left.ProEt) (p : P),
          (c.hom.app P).val.app (op V)
              (((toSheafify (Scheme.ProEt.topology W.left)
                ((Functor.const W.left.ProEtᵒᵖ).obj (AddCommGrpCat.of P))).app (op V)) p) =
            ((toSheafify (Scheme.ProEt.topology Y)
              ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of P))).app
                (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj V))) p := by
  let e := restrictionRingIso Y W B
  let c : siteConstantModuleFunctorGeneral (Scheme.ProEt.topology W.left) B ≅
      siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B ⋙
        SheafOfModules.pushforward (F := restrictionSiteFunctor Y W) e.hom :=
    NatIso.ofComponents (fun P ↦ asIso (restrictionConstantComparison Y W B P)) (by
      intro P Q f
      apply (PresheafOfModules.sheafificationHomEquiv
        (toSheafify (Scheme.ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of B)))).injective
      apply (PresheafOfModules.toPresheaf _).map_injective
      simp only [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
      change toSheafify (Scheme.ProEt.topology W.left)
          ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj P).presheaf ≫
        (((SheafOfModules.toSheaf _).map
          ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology W.left) B).map f)).hom ≫
            ((SheafOfModules.toSheaf _).map
              (restrictionConstantComparison Y W B Q)).hom) =
        toSheafify (Scheme.ProEt.topology W.left)
          ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj P).presheaf ≫
        (((SheafOfModules.toSheaf _).map
          (restrictionConstantComparison Y W B P)).hom ≫
          ((SheafOfModules.toSheaf _).map
            ((SheafOfModules.pushforward (F := restrictionSiteFunctor Y W) e.hom).map
              ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).map f))).hom)
      simp only [← Category.assoc]
      rw [restrictionConstantComparison_fac]
      have hn := toSheafify_naturality (Scheme.ProEt.topology W.left)
        ((PresheafOfModules.toPresheaf _).map
          ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).map f))
      change _ = toSheafify (Scheme.ProEt.topology W.left)
        ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj P).presheaf ≫
          ((SheafOfModules.toSheaf _).map
            ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology W.left) B).map f)).hom at hn
      rw [← hn, Category.assoc]
      change (PresheafOfModules.toPresheaf _).map
          ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).map f) ≫
        (toSheafify (Scheme.ProEt.topology W.left)
          ((siteConstantModulePresheafGeneral (C := W.left.ProEt) B).obj Q).presheaf ≫
            ((SheafOfModules.toSheaf _).map
              (restrictionConstantComparison Y W B Q)).hom) = _
      rw [restrictionConstantComparison_fac]
      ext V p
      exact ConcreteCategory.congr_hom
        (congr_app (toSheafify_naturality (Scheme.ProEt.topology Y)
          ((PresheafOfModules.toPresheaf _).map
            ((siteConstantModulePresheafGeneral (C := Y.ProEt) B).map f)))
          ((restrictionSiteFunctor Y W).op.obj V)) p)
  refine ⟨e, fun V ↦ restrictionRingIso_unit Y W B (op V), c, ?_⟩
  intro P V p
  exact ConcreteCategory.congr_hom
    (congr_app (restrictionConstantComparison_fac Y W B P) (op V)) p

/-- The canonical comparison from successive pullback to restriction, obtained by
inverting the recorded pullback compositor and then applying the localization
comparison. No new inverse image or restriction functor is chosen.
Source: Stacks Tags 098T and 03EH
(blueprint: lem-sfb-proetale-object-pullback-restriction). -/
def proEtaleObjectCompositeRestrictionIso {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (U : Z.ProEt) (hr : WeaklyEtale (U.hom ≫ g)) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} U.hom ≅
      @Functor.sheafPushforwardContinuous U.left.ProEt _ Y.ProEt _
        (MorphismProperty.Over.map (f := U.hom ≫ g) ⊤ hr) Ab.{u + 1} _
        (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.isContinuous_overMap hr) :=
  (upperStarComp Ab.{u + 1} U.hom g).symm ≪≫
    upperStarIsoSheafPushforward Ab.{u + 1} (U.hom ≫ g) hr

/-- The pullback compositor and its composite with restriction are monoidal.
Source: Stacks Tag 098T and Sites and Sheaves, Tag 03EH
(blueprint: lem-sfb-proetale-object-pullback-restriction).

Proof: the pushforward compositor is monoidal for the canonical lax structures.
Its conjugate mate under the composite adjunction is the pullback compositor.
Transposing its tensor and unit equations using the monoidal adjunction units
and counits gives the two monoidal equations for the compositor. Composition
with the monoidal restriction comparison gives the second assertion.
-/
theorem proEtaleObjectPullbackCompMonoidal {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (U : Z.ProEt) (hr : WeaklyEtale (U.hom ≫ g)) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} U.hom g).hom ∧
      NatTrans.IsMonoidal (proEtaleObjectCompositeRestrictionIso g U hr).hom := by
  have hm : NatTrans.IsMonoidal
      ((upperStarComp Ab.{u + 1} U.hom g).symm).hom := by
    exact isMonoidal_conjugateEquiv_symm
      (upperStarLowerStarAdjunction Ab.{u + 1} (U.hom ≫ g))
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} U.hom))
      (lowerStarComp Ab.{u + 1} U.hom g).inv
  let := hm
  have hc : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} U.hom g).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} U.hom g).symm.inv)
  refine ⟨hc, ?_⟩
  dsimp only [proEtaleObjectCompositeRestrictionIso, Iso.trans_hom]
  infer_instance

/-- Module transport along the canonical composite comparison. The target ring
acts through the same ring comparison; the module comparison has precisely the
underlying abelian comparison, including on the regular module. Both functors
preserve finite biproducts, and the natural isomorphism commutes with their maps.
Source: Modules on Sites, Section 03DH
(blueprint: lem-sfb-proetale-object-pullback-restriction).

Proof: the monoidal comparison induces the ring map at R. Its tensor equation
and naturality for the action give the module equation
θ_M γ = γ_res (θ_R ⊗ θ_M). Thus its components are module isomorphisms over θ_R,
natural in M. For the regular module the action is multiplication, so the same
component is θ_R and preserves the unit and multiplication. Pullback preserves
colimits and is exact; restriction preserves finite biproducts sectionwise.
Finite biproducts in module objects are computed on underlying sheaves, so both
module functors preserve them. Naturality for their injections and projections
is the asserted compatibility with finite biproducts, including the empty one.
-/
theorem proEtaleObjectModulePullbackRestriction {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (U : Z.ProEt) (hr : WeaklyEtale (U.hom ≫ g))
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∃ h : IsMonHom (Functor.compAlgHom (upperStar Ab.{u + 1} g)
        (upperStar Ab.{u + 1} U.hom) (proEtaleObjectCompositeRestrictionIso g U hr).hom R),
      ∃ c : (upperStar Ab.{u + 1} g).mapMod R ⋙
            (upperStar Ab.{u + 1} U.hom).mapMod ((upperStar Ab.{u + 1} g).obj R) ≅
          (@Functor.sheafPushforwardContinuous U.left.ProEt _ Y.ProEt _
            (MorphismProperty.Over.map (f := U.hom ≫ g) ⊤ hr) Ab.{u + 1} _
            (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)
            (Scheme.ProEt.isContinuous_overMap hr)).mapMod R ⋙
              @Mod.comap (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1}) _ _
                (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1}) _
                (MonoidalCategory.selfLeftAction _) _ _
                ((upperStar Ab.{u + 1} U.hom).monObjObj ((upperStar Ab.{u + 1} g).obj R)) _
                ((proEtaleObjectCompositeRestrictionIso g U hr).hom.app R) h,
        (∀ M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R,
          (c.hom.app M).hom = (proEtaleObjectCompositeRestrictionIso g U hr).hom.app M.X) ∧
        (c.hom.app (Mod.regular R)).hom =
          (proEtaleObjectCompositeRestrictionIso g U hr).hom.app R ∧
        PreservesFiniteBiproducts ((upperStar Ab.{u + 1} g).mapMod R ⋙
          (upperStar Ab.{u + 1} U.hom).mapMod ((upperStar Ab.{u + 1} g).obj R)) ∧
        PreservesFiniteBiproducts
          ((@Functor.sheafPushforwardContinuous U.left.ProEt _ Y.ProEt _
            (MorphismProperty.Over.map (f := U.hom ≫ g) ⊤ hr) Ab.{u + 1} _
            (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology Y)
            (Scheme.ProEt.isContinuous_overMap hr)).mapMod R ⋙
              @Mod.comap (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1}) _ _
                (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1}) _
                (MonoidalCategory.selfLeftAction _) _ _
                ((upperStar Ab.{u + 1} U.hom).monObjObj ((upperStar Ab.{u + 1} g).obj R)) _
                ((proEtaleObjectCompositeRestrictionIso g U hr).hom.app R) h) := by
  let := (proEtaleObjectPullbackCompMonoidal g U hr).2
  refine ⟨inferInstance, Functor.mapModCompIso _ _
    (proEtaleObjectCompositeRestrictionIso g U hr).hom R,
    fun _ ↦ rfl, rfl, ?_, ?_⟩
  · infer_instance
  · have := Functor.additive_of_iso
      (Functor.mapModCompIso _ _ (proEtaleObjectCompositeRestrictionIso g U hr).hom R)
    infer_instance


end AlgebraicGeometry.ProEtale
