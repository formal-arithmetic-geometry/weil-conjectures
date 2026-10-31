/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import all WeilConjectures.AlgebraicGeometry.CoefficientProjectionSquare
import all WeilConjectures.AlgebraicGeometry.CartesianCoefficientsFiniteFree
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.FiniteDiscreteScalarProjectionCase
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.IntegralFinitePointResolution

/-! # The elementary coefficient cases of ordinary direct-image comparison

Source: blueprint latest, scalar-six direct-image proof, finite rings,
finite-free and finitely presented extensions, localization, and algebraic closure.
(blueprint: lem-route-scalar-direct-image-elementary-cases).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private instance scalarSixRing_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm
private instance scalarSixMap_mon {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem mate_ofNatIsoLeft
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R : B ⥤ A} {M M' : C ⥤ D} {S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (e : L ≅ L') (d : M ≅ M')
    {G : A ⥤ C} {H : B ⥤ D} (α : TwoSquare G L M H) :
    (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft d)
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft G d.inv ≫ α.natTrans ≫ Functor.whiskerRight e.hom H))).natTrans =
      (mateEquiv a b α).natTrans := by
  ext K
  simp [mateEquiv, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    ← Functor.map_comp, Category.assoc]

set_option maxHeartbeats 800000 in
-- Control elaboration of the two derived-adjunction mate transports.
private theorem scalarSixPullHom_flat {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPullHom a f =
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).symm
        (scalarSixChange a X) ≪≫ derivedPullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f ≪≫
        Functor.isoWhiskerLeft (scalarSixChange a Y)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f)).hom := by
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv adjY adjX).injective
  change mateEquiv adjY adjX ((mateEquiv adjY adjX).symm
      (.mk _ _ _ _ (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)) = _
  rw [Equiv.apply_symm_apply]
  have ht := mateEquiv_whiskerTop_whiskerBottom adjY adjX
    (.mk _ _ _ _ (derivedPullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).hom)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).hom
  have hm := congrArg (fun (s : TwoSquare _ _ _ _) ↦
      (s.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).hom)
    (mateEquiv_derivedPullIso_hom (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)
  refine Eq.trans ?_ (Eq.trans (ht.trans hm).symm ?_)
  · ext K
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
    derivedComapLeftDerivedUpperStarIso, derivedComapUpperStarIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    have hi := (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom X)).mapDerivedCategory.map_id ((upperStar Λ'.X f).mapDerivedCategory.obj K)
    let p := ((Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapDerivedCategoryCompIso
        (upperStar Λ.X f)).inv.app K
    let q := (Functor.mapDerivedCategoryNatIso
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)).inv.app K
    let r := ((upperStar Λ'.X f).mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))).hom.app K
    simpa only [Category.assoc] using
      (Category.comp_id (p ≫ q ≫ r)).symm.trans
        (congrArg (fun t ↦ (p ≫ q ≫ r) ≫ t) hi.symm)
  · apply congrArg (mateEquiv adjY adjX)
    ext K
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.equivNatTrans,
      TwoSquare.mk, scalarSixChange, scalarSixAdjunctionLeft]

set_option maxHeartbeats 1000000 in
-- The normalized scalar and geometric mates are compared with their folded adjunctions.
private theorem scalarDirectImageMate_flat {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarDirectImageMate a f =
      derivedPushHom (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f := by
  have hp : scalarDirectImagePullbackData.theta a f =
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).symm
        (scalarSixChange a X) ≪≫ derivedPullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f ≪≫
        Functor.isoWhiskerLeft (scalarSixChange a Y)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f) := by
    apply Iso.ext
    exact (scalarDirectImagePullbackData.thetaNormalization a f).trans
      (scalarSixPullHom_flat a f)
  unfold scalarDirectImageMate
  rw [hp]
  have ht := mate_ofNatIsoLeft (derivedUpperStarLowerStarAdjunction Λ.X f)
    (derivedUpperStarLowerStarAdjunction Λ'.X f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f)
    (.mk _ _ _ _ (derivedPullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)
  simpa only [RootCoordinateFace.adjunction, RootCoordinateFace.upper,
    RootCoordinateFace.lower, moduleObjectDerivedPushforward, Adjunction.mapDerived_eq,
    scalarSixChange,
    scalarSixAdjunctionLeft, TwoSquare.mk, TwoSquare.equivNatTrans,
    derivedUpperStarLowerStarAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, Category.assoc] using
    ht.trans (derivedPushHom_eq_mateEquiv (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm

private instance integralFlat (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ell h) Z)) :=
  fun Z ↦ (cartesianCoefficients_finiteFree.{u} ell h).2.2 Z |>.1

set_option maxHeartbeats 800000 in
-- Normalize finite coproducts and their condensed continuous-basis comparison.
private theorem integralPush (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (derivedPushHom (finiteCoefficientIntegersPointMap ell h) f) := by
  classical
  let : Algebra (PadicAlgCl.integers ell E.1) (PadicAlgCl.integers ell F.1) :=
    (finiteCoefficientIntegersMap ell h).toAlgebra
  obtain ⟨b⟩ := (cartesianCoefficients_finiteFree.{u} ell h).1
  obtain ⟨e, _⟩ := continuous_basis_iso
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _)
    (finiteCoefficientDegree ell h) b (integral_coordinates_continuous ell h b)
  let R := Profinite.padicIntegersRingObj.{u} ell E.1
  let S := Profinite.padicIntegersRingObj.{u} ell F.1
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) :=
    IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  let n := finiteCoefficientDegree ell h
  let I := ULift.{u + 1} (Fin n)
  let e' : (∐ fun _ : I ↦ Mod.regular R) ≅
      (Mod.comap (finiteCoefficientIntegersPointMap ell h)).obj (Mod.regular S) :=
    Sigma.reindex Equiv.ulift (fun _ : Fin n ↦ Mod.regular R) ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ e
  exact finitePush_of_pointCopower f R S (finiteCoefficientIntegersPointMap ell h) I e'

private theorem localizedPush (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (Profinite.padicIntegersRingObj ell E.1) X))
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X K) :
    IsIso ((derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ell E) f).app K) := by
  obtain ⟨n, hn⟩ := hK.1.1
  have : K.IsGE n := hn
  exact isIso_derivedPushHom_app_padicIntegers_of_isGE ell E f K n

private theorem qbarPush (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (Profinite.continuousMapRingObj E.1) X))
    (hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ell E) f).app K) := by
  exact isIso_derivedPushHom_padicAlgCl_of_boundedBelow ell E f ⟨K, hK.1.1⟩

section FlatCases
set_option allowUnsafeReducibility true
attribute [local reducible] CommMon.homMk Mon.Hom.mk'
attribute [local irreducible] scalarSixChange scalarDirectImageMate

set_option maxHeartbeats 1600000 in
-- Four coefficient presentations require normalizing the same derived mate.
private theorem flatCases
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell F.1⟩)
      (_ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj F.1⟩)
      (_ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj E.1⟩)
      (_ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicAlgClRingObj ell⟩)
      (_ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ell E),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) := by
  have hq : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w]
    infer_instance
  have hqs : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w]
    infer_instance
  let : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  let : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E F h a ha K _hK
    have ha' : a = CommMon.homMk (Mon.Hom.mk'
        (finiteCoefficientIntegersPointMap ell h)) := CommMon.hom_ext _ _ ha
    subst a
    let : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ell h) Z)) :=
      inferInstance
    rw [scalarDirectImageMate_flat]
    have := integralPush ell h f.left
    simpa only [scalarSixChange, RootCoordinateFace.lower, moduleObjectDerivedPushforward,
      CommMon.homMk, Mon.Hom.mk'] using (inferInstanceAs
        (IsIso ((derivedPushHom (finiteCoefficientIntegersPointMap ell h) f.left).app K)))
  · intro E F h a ha K _hK
    have ha' : a = CommMon.homMk (Mon.Hom.mk'
        (Profinite.padicSubfieldRingObjMap ell h)) := CommMon.hom_ext _ _ ha
    subst a
    let : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ell h) Z)) :=
      inferInstance
    rw [scalarDirectImageMate_flat]
    simpa only [scalarSixChange, RootCoordinateFace.lower, moduleObjectDerivedPushforward,
      CommMon.homMk, Mon.Hom.mk'] using (inferInstanceAs
        (IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjMap ell h) f.left).app K)))
  · intro E a ha K hK
    have ha' : a = CommMon.homMk (Mon.Hom.mk'
        (padicIntegersRingObjToContinuousMapRingObj ell E)) := CommMon.hom_ext _ _ ha
    subst a
    let : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars
          (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ell E) Z)) :=
      inferInstance
    rw [scalarDirectImageMate_flat]
    simpa only [scalarSixChange, RootCoordinateFace.lower, moduleObjectDerivedPushforward,
      CommMon.homMk, Mon.Hom.mk'] using localizedPush ell E f.left K hK.1
  · intro E a ha K hK
    have ha' : a = CommMon.homMk (Mon.Hom.mk'
        (Profinite.padicSubfieldRingObjToPadicAlgCl ell E)) := CommMon.hom_ext _ _ ha
    subst a
    let : ∀ Z : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ell E) Z)) :=
      inferInstance
    rw [scalarDirectImageMate_flat]
    simpa only [scalarSixChange, RootCoordinateFace.lower, moduleObjectDerivedPushforward,
      CommMon.homMk, Mon.Hom.mk'] using qbarPush ell E f.left K hK.1

end FlatCases

open IntegralFiniteScalar

private theorem restrictionReflectsIsomorphisms {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (Z : Scheme.{u}) : (restriction a Z).ReflectsIsomorphisms := by
  let F : ModuleRingedComparison.internalModules Λ'.X Z ⥤
      ModuleRingedComparison.internalModules Λ.X Z :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  have : F.ReflectsIsomorphisms := by
    refine ⟨?_⟩
    intro M N f hf
    have : IsIso f.hom := by
      change IsIso ((Mod.forget (condensedRingObj Λ.X Z)).map (F.map f))
      infer_instance
    have : IsIso ((Mod.forget (condensedRingObj Λ'.X Z)).map f) := by
      change IsIso f.hom
      infer_instance
    exact isIso_of_reflects_iso f (Mod.forget (condensedRingObj Λ'.X Z))
  change F.mapDerivedCategory.ReflectsIsomorphisms
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem mate_app_homEquiv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {M : C ⥤ D} {S : D ⥤ C}
    (adj : L ⊣ R) (adj' : M ⊣ S) {G : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G L M H) (K : B) :
    adj'.homEquiv _ _ (α.natTrans.app (R.obj K) ≫ H.map (adj.counit.app K)) =
      (mateEquiv adj adj' α).natTrans.app K := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  exact (mateEquiv_counit adj adj' α K).symm

private theorem gamma_eq_scalarDirectImageMate {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    gamma scalarDirectImagePullbackData a f K = (scalarDirectImageMate a f).app K := by
  have ht := mate_app_homEquiv (RootCoordinateFace.adjunction Λ.X f)
    (RootCoordinateFace.adjunction Λ'.X f)
    (.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv) K
  simpa only [gamma, geometricAdjunction, scalarSixPull, RootCoordinateFace.upper,
    RootCoordinateFace.lower, RootCoordinateFace.adjunction, scalarDirectImageMate,
    Adjunction.mapDerived_eq, derivedUpperStarLowerStarAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory, TwoSquare.mk, TwoSquare.natTrans,
    Functor.comp_obj, Functor.id_obj] using ht

set_option maxHeartbeats 800000 in
-- Keep the resolution comparison and its geometric adjunctions folded.
private theorem perfectMate {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (P : ShortComplex (PointModules Λ))
    (t : P.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hP : P.ShortExact) (r : ℕ)
    (e₁ : P.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : P.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    IsIso ((scalarDirectImageMate a f).app K) := by
  let D := scalarDirectImagePullbackData
  obtain ⟨hflat, β, hnorm, hpull, hmate⟩ :=
    derivedAssertions_of_finite_integral_resolution D a P t hP r e₁ e₂
  have hp := finiteFreeScalarProjection Λ P r e₁ e₂ f K
  have : (restriction a Y).ReflectsIsomorphisms :=
    restrictionReflectsIsomorphisms a Y
  have hc : IsIso ((β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
      (restriction a Y).map (gamma D a f K) ≫
      (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
      (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K)) := by
    rw [hmate X Y f K]
    exact hp
  have hi : IsIso ((restriction a Y).map (gamma D a f K)) := by
    have htail := (isIso_comp_left_iff ((β Y).hom.app
      ((moduleObjectDerivedPushforward Λ.X f).obj K)) _).mp hc
    exact (isIso_comp_right_iff
      ((restriction a Y).map (gamma D a f K))
      ((restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
        (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K))).mp
      (by simpa only [Category.assoc] using htail)
  have : IsIso (gamma D a f K) := isIso_of_reflects_iso _ (restriction a Y)
  rw [← gamma_eq_scalarDirectImageMate a f K]
  exact inferInstanceAs (IsIso (gamma D a f K))

section NormalizedProjection
set_option allowUnsafeReducibility true
attribute [local reducible] QuotientChange.D QuotientChange.L QuotientChange.F
  moduleObjectDerivedPullback

set_option maxHeartbeats 800000 in
-- Compare the two presentations of the scalar-adjunction mate.
private theorem scalarSixPullHom_normalized {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y ⋙ QuotientChange.L Λ'.X f ≅
      QuotientChange.L Λ.X f ⋙ QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
    (hb : QuotientChange.PullNormalized (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f b) :
    scalarSixPullHom a f =
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).symm
        (scalarSixChange a X) ≪≫ b.symm ≪≫
        Functor.isoWhiskerLeft (scalarSixChange a Y)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f)).hom := by
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv adjY adjX).injective
  change mateEquiv adjY adjX ((mateEquiv adjY adjX).symm
      (.mk _ _ _ _ (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)) = _
  rw [Equiv.apply_symm_apply]
  have ht := mateEquiv_whiskerTop_whiskerBottom adjY adjX
    (.mk _ _ _ _ b.inv)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).hom
  have hb' : mateEquiv adjY adjX (.mk _ _ _ _ b.inv) =
      .mk _ _ _ _ (QuotientChange.normalizationRestrictionPull
        (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv := by
    have h := QuotientChange.normalized_inverse
      (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f b hb
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv adjY adjX (.mk _ _ _ _ b.inv)).natTrans = _
    have he := congrArg (fun t ↦ (mateEquiv adjY adjX (.mk _ _ _ _ t)).natTrans) h
    exact he.trans (congrArg TwoSquare.natTrans
      ((mateEquiv adjY adjX).apply_symm_apply
        (.mk _ _ _ _ (QuotientChange.normalizationRestrictionPull
        (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)))
  have hm := congrArg (fun (s : TwoSquare _ _ _ _) ↦
      (s.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).hom) hb'
  refine Eq.trans ?_ (Eq.trans (ht.trans hm).symm ?_)
  · ext K
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
    TwoSquare.natTrans, id_eq, QuotientChange.V, QuotientChange.V₀,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    QuotientChange.normalizationRestrictionPull, derivedComapUpperStarIso,
    leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    have hi := (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom X)).mapDerivedCategory.map_id ((upperStar Λ'.X f).mapDerivedCategory.obj K)
    let p := ((Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapDerivedCategoryCompIso
        (upperStar Λ.X f)).inv.app K
    let q := (Functor.mapDerivedCategoryNatIso
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)).inv.app K
    let r := ((upperStar Λ'.X f).mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))).hom.app K
    simpa only [Category.assoc] using
      (Category.comp_id (p ≫ q ≫ r)).symm.trans
        (congrArg (fun t ↦ (p ≫ q ≫ r) ≫ t) hi.symm)
  · apply congrArg (mateEquiv adjY adjX)
    ext K
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.equivNatTrans,
      TwoSquare.mk, scalarSixChange, scalarSixAdjunctionLeft, QuotientChange.D,
      QuotientChange.L, moduleObjectDerivedPullback]

set_option maxHeartbeats 1000000 in
-- Normalize both geometric adjunctions before applying the projection criterion.
private theorem scalarDirectImageMate_isIso_iff_projection {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    IsIso ((scalarDirectImageMate a f).app K) ↔
      IsIso (QuotientChange.scalarProjection (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f K) := by
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules Λ.X T) := fun T ↦
    IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ.X T)
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ.X T) := fun T ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules Λ'.X T) := fun T ↦
    IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ'.X T)
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ'.X T) := fun T ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  obtain ⟨tX, tY, b, sX, sY, hX, hY, hb, hsX, hsY, htX, htY, hp⟩ :=
    QuotientChange.internal_scalar_pullback_normalization
      (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
  have hθ : scalarDirectImagePullbackData.theta a f =
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).symm
        (scalarSixChange a X) ≪≫ b.symm ≪≫
        Functor.isoWhiskerLeft (scalarSixChange a Y)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f) := by
    apply Iso.ext
    exact (scalarDirectImagePullbackData.thetaNormalization a f).trans
      (scalarSixPullHom_normalized a f b hb)
  have heq : scalarDirectImageMate a f =
      QuotientChange.rho (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f b := by
    unfold scalarDirectImageMate
    rw [hθ]
    have ht := mate_ofNatIsoLeft (derivedUpperStarLowerStarAdjunction Λ.X f)
      (derivedUpperStarLowerStarAdjunction Λ'.X f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f)
      (.mk _ _ _ _ b.hom)
    simpa only [RootCoordinateFace.adjunction, RootCoordinateFace.upper,
      RootCoordinateFace.lower, moduleObjectDerivedPushforward, Adjunction.mapDerived_eq,
      scalarSixChange, scalarSixAdjunctionLeft, TwoSquare.mk, TwoSquare.equivNatTrans,
      derivedUpperStarLowerStarAdjunction, leftDerivedUpperStarIsoMapDerivedCategory,
      Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Category.assoc, QuotientChange.rho, QuotientChange.adj,
      QuotientChange.L, QuotientChange.F, QuotientChange.D,
      moduleObjectDerivedPullback, QuotientChange.extension, id_eq,
      TwoSquare.natTrans] using ht
  rw [heq]
  exact (QuotientChange.internal_scalar_mate_projection
    (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f tX tY b hX hY hb).2.2.2.2.1 K

end NormalizedProjection

attribute [local irreducible] scalarSixChange scalarDirectImageMate

private theorem scalarSixChange_equivalence_local {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') [IsIso a] (X : Scheme.{u}) :
    (scalarSixChange a X).IsEquivalence := by
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have ha : IsIso a.hom.hom := inferInstance
  have hφ : IsIso (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X) := by
    change IsIso ((upperStarFromPoint X).map a.hom.hom)
    infer_instance
  let : (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).isEquivalence_functor
  unfold scalarSixChange
  exact (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).isEquivalence_left_of_isEquivalence_right

private theorem scalarDirectImageMate_isIso_of_iso_local {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') [IsIso a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarDirectImageMate a f) := by
  let := scalarSixChange_equivalence_local a X
  let := scalarSixChange_equivalence_local a Y
  have : IsIso (TwoSquare.mk (scalarSixChange a Y) (RootCoordinateFace.upper Λ.X f)
      (RootCoordinateFace.upper Λ'.X f) (scalarSixChange a X)
      (scalarDirectImagePullbackData.theta a f).inv).natTrans :=
    inferInstanceAs (IsIso (scalarDirectImagePullbackData.theta a f).inv)
  unfold scalarDirectImageMate
  exact isIso_mateEquiv_of_isEquivalence
    (RootCoordinateFace.adjunction Λ.X f) (RootCoordinateFace.adjunction Λ'.X f)
    (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)

-- Preserve the existing quantified binder names, including proof-irrelevant hypotheses.
set_option linter.unusedVariables false in
set_option maxHeartbeats 1500000 in
-- Assemble seven clauses with several derived-category presentations.
/-- Invertibility of the normalized mate for the six elementary coefficient maps
and the algebraic-closure identity. Composite maps are not asserted here.

Source: blueprint latest, `det-prop-scalar-six-direct-image.proof.md`,
Finite rings; Finite free and finitely presented coefficient extensions;
localization; algebraic closure; Formal properties for the identity.
(blueprint: lem-route-scalar-direct-image-elementary-cases).

Proof: cancel the structure maps to obtain qcqs geometry. The finite discrete
projection step is isolated in finiteDiscreteScalarProjectionCase; the normalized
scalar and geometric adjunctions identify its invertibility with that of the mate.
For each flat coefficient
map, compute the scalar-adjunction mate of restriction/pullback, transport the
geometric adjunction along its canonical derived comparison, and cancel its unit
and counit. This identifies scalarDirectImageMate with derivedPushHom. A continuous
finite basis of O_F over O_E identifies its point module with a finite copower of
O_E; the finite-copower direct-image criterion applies. For E to F use the existing
finite-subfield comparison. For localization and algebraic closure extract a lower
bound from bounded constructibility and apply the published bounded-below comparisons.
For O_E to finite A use integralFinitePointResolution. The finite-free derived
comparison identifies restricted scalar extension with its two-term point model;
the finite-free projection theorem makes the restricted mate invertible. Restriction
reflects isomorphisms, so the actual mate is invertible. Finally scalar extension
along an isomorphism is an equivalence, and the mate equivalence theorem proves the
identity-coefficient clause for every unbounded input. -/
theorem scalarDirectImageElementaryCases
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
      (φ : A →+* B)
      (a : (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing B⟩)
      (ha : ∀ (P : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op P)) (x : P),
        ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (cartesianFinitePointRing A) X.left),
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell F.1⟩)
      (ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj F.1⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj E.1⟩)
      (ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicAlgClRingObj ell⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ell E),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (A : Type u) [CommRing A] [Finite A]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing A⟩)
      (ha : IsIntegralFiniteScalarMap ell E A a),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules
        (Profinite.padicAlgClRingObj ell) X.left),
      IsIso ((scalarDirectImageMate
        (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u})) f.left).app K))  := by
  have hflat := flatCases ell k (X := X) (Y := Y) f
  refine ⟨?_, hflat.1, hflat.2.1, hflat.2.2.1, hflat.2.2.2, ?_, ?_⟩
  · intro A B _ _ _ _ hA hB φ a ha K hK
    exact (scalarDirectImageMate_isIso_iff_projection a f.left K).2
      (finiteDiscreteScalarProjectionCase ell k f A B hA hB φ a ha K hK)
  · intro E A _ _ hA a ha K _hK
    obtain ⟨P, r, hP, ⟨e₁⟩, ⟨e₂⟩, ⟨t⟩⟩ :=
      integralFinitePointResolution ell E A hA a ha
    exact perfectMate a P t hP r e₁ e₂ f.left K
  · intro K
    let : IsIso (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u})) := inferInstance
    have h := scalarDirectImageMate_isIso_of_iso_local
      (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u})) f.left
    let : IsIso (scalarDirectImageMate
      (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u})) f.left) := h
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
