/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

/-! # Unit normalization of finite intrinsic pullback

Source: Stacks 00YV and 07A6, uniqueness of adjoints and exact localization.
(blueprint: lem-sf-finite-intrinsic-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u
namespace WeilConjectures

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

end WeilConjectures

private theorem conjugateRight_unit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (E : A ≌ A') (J : B ≌ B') {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) (Ri : B' ⥤ A') (c : J.functor ⋙ Ri ≅ R ⋙ E.functor)
    (N : A') :
    (conjugateRight E J a Ri c).unit.app N = E.counitIso.inv.app N ≫
      E.functor.map (a.unit.app (E.inverse.obj N)) ≫
        c.inv.app (L.obj (E.inverse.obj N)) := by
  simp only [conjugateRight, Adjunction.ofNatIsoRight_unit,
    Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]
  have hn := c.inv.naturality (J.unitIso.hom.app (L.obj (E.inverse.obj N)))
  dsimp only [Functor.comp_map] at hn
  change E.counitIso.inv.app N ≫ E.functor.map (a.unit.app (E.inverse.obj N)) ≫
    E.functor.map (R.map (J.unitIso.hom.app _)) ≫ c.inv.app _ ≫
      Ri.map (J.counitIso.hom.app _) = _
  erw [reassoc_of% hn]
  rw [← Ri.map_comp]
  simp only [Equivalence.functor_unitIso_comp, Ri.map_id, Category.comp_id]

private theorem normalized_inverseMate_unit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (E : A ≌ A') (J : B ≌ B') {L : A ⥤ B} {R : B ⥤ A}
    {Li : A' ⥤ B'} {Ri : B' ⥤ A'} (a : L ⊣ R) (b : Li ⊣ Ri)
    (c : J.functor ⋙ Ri ≅ R ⋙ E.functor)
    (s : E.functor ⋙ Li ≅ L ⋙ J.functor)
    (hs : (mateEquiv a b s.hom).natTrans = c.inv)
    (N : A') :
    b.unit.app N ≫ Ri.map (Li.map (E.counitIso.inv.app N) ≫
      s.hom.app (E.inverse.obj N)) =
        (conjugateRight E J a Ri c).unit.app N := by
  rw [conjugateRight_unit, Ri.map_comp, ← Category.assoc]
  have hn := b.unit.naturality (E.counitIso.inv.app N)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn]
  rw [Category.assoc]
  have hu := unit_mateEquiv a b s.hom (E.inverse.obj N)
  change E.functor.map (a.unit.app _) ≫
    (mateEquiv a b s.hom).natTrans.app _ = _ at hu
  rw [hs] at hu
  exact congrArg (fun z ↦ E.counitIso.inv.app N ≫ z) hu.symm

private theorem mate_right_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' S' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (e : R' ≅ S') (s : G ⋙ L' ⟶ L ⋙ H) :
    (mateEquiv a (b.ofNatIsoRight e) s).natTrans =
      (mateEquiv a b s).natTrans ≫ Functor.whiskerLeft H e.hom := by
  ext M
  simp only [mateEquiv_apply, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    TwoSquare.mk, TwoSquare.natTrans, Category.id_comp,
    Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]
  change b.unit.app (G.obj (R.obj M)) ≫ e.hom.app _ ≫
      S'.map (s.app (R.obj M)) ≫ S'.map (H.map (a.counit.app M)) =
    b.unit.app (G.obj (R.obj M)) ≫ R'.map (s.app (R.obj M)) ≫
      R'.map (H.map (a.counit.app M)) ≫ e.hom.app (H.obj M)
  erw [← e.hom.naturality_assoc, ← e.hom.naturality]
  rfl

private theorem pushforwardCongr_eq {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [Functor.IsContinuous F J K] {S : Sheaf J RingCat} {R : Sheaf K RingCat}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R} (h : φ = ψ) :
    SheafOfModules.pushforwardCongr h =
      eqToIso (congrArg (fun q ↦ SheafOfModules.pushforward (F := F) q) h) := by
  subst ψ
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  rfl

/-- The ringed-to-intrinsic pullback bridge is the conjugate of the normalized
ordinary scalar inverse mate.
Source: Stacks 00YV; the uniqueness clause of openSquarePullbackModel_existsUnique.
(blueprint: lem-sf-finite-intrinsic-pullback-normalization).

Proof: the inverse mate's unit equation and the coefficient equivalence triangle
identities show that the displayed conjugate preserves the actual intrinsic unit.
Evaluate that equation on every section. The uniqueness clause of the prescribed
bridge identifies the two isomorphisms. This uses neither tensor products nor
resolutions and holds for empty schemes and the zero ring. -/
theorem finiteIntrinsicOrdinaryPullbackNormalization
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    openSquarePullbackModel R f =
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence Y R).counitIso.symm
          (proEtaleConstantRingPullback R f) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y R).inverse
          (finiteScalarOrdinaryPullbackComparison R f) := by
  let EX := sfIntrinsicModuleEquivalence X R
  let EY := sfIntrinsicModuleEquivalence Y R
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) f
  let b := proEtaleConstantRingAdjunction R f
  let d := openSquare_directImageModel R f
  have hd : d = eqToIso (finiteScalarConstantPushforward_eq R f) := by
    exact pushforwardCongr_eq _
  let c := sfIntrinsicDirectImageComparison f R
  let s := finiteScalarOrdinaryPullbackComparison R f
  let e : proEtaleConstantRingPullback R f ≅ sfIntrinsicPullback R f :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight EY.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EY.inverse s
  apply (openSquarePullbackModel_existsUnique R f).unique
    (openSquarePullbackModel_existsUnique R f).exists.choose_spec
  intro M V x
  have hs : (mateEquiv a (b.ofNatIsoRight d) s.hom).natTrans = c.inv := by
    rw [mate_right_iso]
    have h : (mateEquiv a b s.hom).natTrans =
        (c.symm ≪≫ Functor.isoWhiskerLeft EX.functor d.symm).hom := by
      rw [hd]
      unfold s finiteScalarOrdinaryPullbackComparison
      exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply _)
    rw [h]
    apply NatTrans.ext
    funext K
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj, EX]
  have hu := normalized_inverseMate_unit EY EX a (b.ofNatIsoRight d) c s hs M
  change (b.ofNatIsoRight d).unit.app M ≫ _ =
    (sfIntrinsicConstantModuleAdjunction f R).unit.app M at hu
  rw [Adjunction.ofNatIsoRight_unit] at hu
  have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) x) hu
  simp only [NatTrans.comp_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hv
  change ((e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V)))
    (((b.unit.app M).val.app (Opposite.op V)) x) =
      ((sfIntrinsicConstantModuleAdjunction f R).unit.app M).val.app (Opposite.op V) x at hv
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using hv

/-- The ringed-to-intrinsic pullback bridge is the conjugate of the normalized
ordinary scalar inverse mate.
Source: Stacks 00YV; the uniqueness clause of openSquarePullbackModel_existsUnique.
(blueprint: lem-sf-finite-intrinsic-pullback-normalization).

Proof: the inverse mate's unit equation and the coefficient equivalence triangle
identities show that the displayed conjugate preserves the actual intrinsic unit.
Evaluate that equation on every section. The uniqueness clause of the prescribed
bridge identifies the two isomorphisms. This uses neither tensor products nor
resolutions and holds for empty schemes and the zero ring. -/
theorem finiteIntrinsicOrdinaryPullbackNormalization
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    openSquarePullbackModel R f =
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence Y R).counitIso.symm
          (proEtaleConstantRingPullback R f) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y R).inverse
          (finiteScalarOrdinaryPullbackComparison R f) := by
  let EX := sfIntrinsicModuleEquivalence X R
  let EY := sfIntrinsicModuleEquivalence Y R
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) f
  let b := proEtaleConstantRingAdjunction R f
  let d := openSquare_directImageModel R f
  have hd : d = eqToIso (finiteScalarConstantPushforward_eq R f) := by
    exact pushforwardCongr_eq _
  let c := sfIntrinsicDirectImageComparison f R
  let s := finiteScalarOrdinaryPullbackComparison R f
  let e : proEtaleConstantRingPullback R f ≅ sfIntrinsicPullback R f :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight EY.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EY.inverse s
  apply (openSquarePullbackModel_existsUnique R f).unique
    (openSquarePullbackModel_existsUnique R f).exists.choose_spec
  intro M V x
  have hs : (mateEquiv a (b.ofNatIsoRight d) s.hom).natTrans = c.inv := by
    rw [mate_right_iso]
    have h : (mateEquiv a b s.hom).natTrans =
        (c.symm ≪≫ Functor.isoWhiskerLeft EX.functor d.symm).hom := by
      rw [hd]
      unfold s finiteScalarOrdinaryPullbackComparison
      exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply _)
    rw [h]
    apply NatTrans.ext
    funext K
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj, EX]
  have hu := normalized_inverseMate_unit EY EX a (b.ofNatIsoRight d) c s hs M
  change (b.ofNatIsoRight d).unit.app M ≫ _ =
    (sfIntrinsicConstantModuleAdjunction f R).unit.app M at hu
  rw [Adjunction.ofNatIsoRight_unit] at hu
  have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) x) hu
  simp only [NatTrans.comp_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hv
  change ((e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V)))
    (((b.unit.app M).val.app (Opposite.op V)) x) =
      ((sfIntrinsicConstantModuleAdjunction f R).unit.app M).val.app (Opposite.op V) x at hv
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using hv
