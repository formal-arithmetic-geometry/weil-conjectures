/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAdjunctionCoordinates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
public import Mathlib.CategoryTheory.Category.Cat
public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.SingleAlphaRestrictionNormalization
public import WeilConjectures.CategoryTheory.Derived.DerivedEquivalenceCancellation
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
public import WeilConjectures.CategoryTheory.EquivalenceCubeTransport.EquivalenceCubeTransport
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteIntrinsicPullbackNormalization

/-! # Coordinates for one native finite coefficient category

Source: Stacks 00YV, 03DI and 07A7; finite coefficient realization in
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-finite-native-alpha-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf presheafToSheaf Functor.leftAdjoint
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible] StrictTower.modulePullback

variable (A : Type u) [CommRing A] [Finite A]

@[irreducible] private def nativeScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y A).functor ⋙
        StrictTower.modulePullback (ULift.{u + 1} A) f ≅
      upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  finiteScalarOrdinaryPullbackComparison A f

private def cancelCoordinates
    {C D Cn Dn : Type*} [Category C] [Category D] [Category Cn] [Category Dn]
    (e : C ≌ Cn) (f : D ≌ Dn) (L : C ⥤ D) (Ln : Cn ⥤ Dn)
    (q : Ln ≅ e.inverse ⋙ L ⋙ f.functor) : Ln ⋙ f.inverse ≅ e.inverse ⋙ L :=
  Functor.isoWhiskerRight q f.inverse ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerLeft L f.unitIso.symm) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.rightUnitor L)

private theorem cancelCoordinates_unit
    {C D Cn Dn : Type*} [Category C] [Category D] [Category Cn] [Category Dn]
    (e : C ≌ Cn) (f : D ≌ Dn) {J : C ⥤ D} {P : D ⥤ C} (a : J ⊣ P)
    (Jn : Cn ⥤ Dn) (Pn : Dn ⥤ Cn)
    (q : Pn ≅ f.inverse ⋙ P ⋙ e.functor)
    (z : Jn ≅ e.inverse ⋙ J ⋙ f.functor)
    (η : 𝟭 Cn ⟶ Jn ⋙ Pn)
    (h : ∀ N, η.app N ≫ q.hom.app (Jn.obj N) ≫
      (f.inverse ⋙ P ⋙ e.functor).map (z.hom.app N) =
      ((e.symm.toAdjunction.comp a).comp f.toAdjunction).unit.app N) (N : Cn) :
    e.inverse.map (η.app N) ≫ (cancelCoordinates f e P Pn q).hom.app (Jn.obj N) ≫
      P.map ((cancelCoordinates e f J Jn z).hom.app N) =
        a.unit.app (e.inverse.obj N) := by
  dsimp only [Functor.comp_map] at h
  simp only [cancelCoordinates, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := e.unitIso.inv.naturality (P.map (f.inverse.map (z.hom.app N)))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
  rw [← reassoc_of% hn]
  slice_lhs 1 3 => rw [← e.inverse.map_comp, ← e.inverse.map_comp, h]
  simp only [Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Equivalence.symm_functor, Equivalence.symm_inverse,
    Equivalence.unit, Equivalence.counitInv, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc, Category.comp_id]
  have hη := e.unitIso.inv.naturality
    (a.unit.app (e.inverse.obj N) ≫ P.map (f.unitIso.hom.app (J.obj (e.inverse.obj N))))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hη
  simp only [Functor.map_comp, Category.assoc] at hη
  rw [reassoc_of% hη]
  rw [← e.unit_app_inverse]
  simp only [Equivalence.unit, Iso.hom_inv_id_app_assoc]
  rw [← P.map_comp, Iso.hom_inv_id_app]
  simp

private def ordinaryPullCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StrictTower.modulePullback (ULift.{u + 1} A) f ⋙
        (sfIntrinsicModuleEquivalence X A).inverse ≅
      (sfIntrinsicModuleEquivalence Y A).inverse ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
  cancelCoordinates (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence X A)
    _ _ (openSquarePullbackModel A f)

private def ordinaryShriekCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    StrictTower.moduleJ (ULift.{u + 1} A) j ⋙
        (sfIntrinsicModuleEquivalence Y A).inverse ≅
      (sfIntrinsicModuleEquivalence X A).inverse ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j :=
  cancelCoordinates (sfIntrinsicModuleEquivalence X A) (sfIntrinsicModuleEquivalence Y A)
    _ _ (compactSupportOpenModel j A)

private theorem ordinary_open_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (N : StrictTower.Modules (ULift.{u + 1} A) X) :
    (sfIntrinsicModuleEquivalence X A).inverse.map
        ((StrictTower.moduleJAdj (ULift.{u + 1} A) j).unit.app N) ≫
      (ordinaryPullCoordinates A j).hom.app
        ((StrictTower.moduleJ (ULift.{u + 1} A) j).obj N) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).map
        ((ordinaryShriekCoordinates A j).hom.app N) =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).unit.app
        ((sfIntrinsicModuleEquivalence X A).inverse.obj N) := by
  exact cancelCoordinates_unit _ _ _ _ _ _ _ _ (finiteOpen_unit A j) N

private def directForward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence X A).functor ⋙
        StrictTower.moduleDirectImage (ULift.{u + 1} A) f ≅
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        (sfIntrinsicModuleEquivalence Y A).functor :=
  Functor.isoWhiskerLeft _ (compactSupportDirectModel f A) ≪≫
    sfIntrinsicDirectImageComparison f A

private theorem directForward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (W : Y.ProEtᵒᵖ) (m : M.obj.obj ((proEtaleBaseChange f).op.obj W)) :
    ((directForward A f).hom.app M).val.app W
        (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m) =
      sfIntrinsicRealizationUnit Y A
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj M) W m := by
  change (((sfIntrinsicDirectImageComparison f A).hom.app M).val.app W)
      ((((compactSupportDirectModel f A).hom.app
        ((sfIntrinsicModuleEquivalence X A).functor.obj M)).val.app W)
          (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m)) = _
  unfold compactSupportDirectModel
  erw [SheafOfModules.pushforwardCongr_hom_app_val_app]
  exact (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose_spec M W m

private theorem realization_unit_map {X : Scheme.{u}}
    {M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence X A).functor.map f).val.app W
        (sfIntrinsicRealizationUnit X A M W m) =
      sfIntrinsicRealizationUnit X A N W (f.hom.app W m) := by
  unfold sfIntrinsicModuleEquivalence
  exact (congrArg (fun g ↦ g.app W m)
    ((PresheafOfModules.sheafificationAdjunction
      (finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
        ((finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1} A)).map f.hom))).symm

private theorem realization_unit_restrict {X : Scheme.{u}}
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    {W W' : X.ProEtᵒᵖ} (f : W ⟶ W') (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence X A).functor.obj M).val.map f
        (sfIntrinsicRealizationUnit X A M W m) =
      sfIntrinsicRealizationUnit X A M W' (M.obj.map f m) := by
  unfold sfIntrinsicModuleEquivalence
  exact (congrArg (fun g ↦ g m)
    (((PresheafOfModules.sheafificationAdjunction
      (finiteCoefficientIntrinsicScalarMap X A)).unit.app
        ((finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1} A)).obj M.obj)).naturality f)).symm

private theorem directForward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (StrictTower.moduleDirectImage (ULift.{u + 1} A) g).map
        ((directForward A f).hom.app M) ≫
      (directForward A g).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj M) ≫
      (sfIntrinsicModuleEquivalence Z A).functor.map
        ((lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app M) =
    (StrictTower.moduleRComp (ULift.{u + 1} A) f g).hom.app
        ((sfIntrinsicModuleEquivalence X A).functor.obj M) ≫
      (directForward A (f ≫ g)).hom.app M := by
  ext W x
  let U := (proEtaleBaseChange f).op.obj ((proEtaleBaseChange g).op.obj W)
  let η := ((PresheafOfModules.evaluation _ U).mapIso
    ((AlgebraicGeometry.Scheme.intrinsicUnitIso X A).app M)).toLinearEquiv
  obtain ⟨m, hm⟩ := η.surjective x
  change M.obj.obj U at m
  change sfIntrinsicRealizationUnit X A M U m = x at hm
  subst x
  change ((sfIntrinsicModuleEquivalence Z A).functor.map
      ((lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app M)).val.app W
      (((directForward A g).hom.app _).val.app W
        (((directForward A f).hom.app M).val.app ((proEtaleBaseChange g).op.obj W)
          (sfIntrinsicRealizationUnit X A M U m))) =
    ((directForward A (f ≫ g)).hom.app M).val.app W
      (((StrictTower.moduleRComp (ULift.{u + 1} A) f g).hom.app _).val.app W
        (sfIntrinsicRealizationUnit X A M U m))
  rw [directForward_unit]
  erw [directForward_unit]
  erw [realization_unit_map]
  have hr := (StrictTower.moduleRComp_existsUnique (ULift.{u + 1} A) f g).choose_spec.1
    ((sfIntrinsicModuleEquivalence X A).functor.obj M) W.unop
      (sfIntrinsicRealizationUnit X A M U m)
  change (((StrictTower.moduleRComp (ULift.{u + 1} A) f g).hom.app _).val.app W) _ = _
    at hr
  erw [hr]
  erw [realization_unit_restrict, directForward_unit]
  congr 1

private theorem directForward_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
      (proEtaleConstantRingAdjunction A f)
      (nativeScalarPull A f).hom).natTrans =
      (directForward A f).inv := by
  let r := (sfIntrinsicDirectImageComparison f A).symm ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).functor
      (eqToIso (finiteScalarConstantPushforward_eq A f)).symm
  unfold nativeScalarPull finiteScalarOrdinaryPullbackComparison
  dsimp only
  change ((mateEquiv _ _) ((mateEquiv _ _).symm
    (TwoSquare.mk _ _ _ _ r.hom))).natTrans = _
  rw [Equiv.apply_symm_apply]
  simp only [directForward, Iso.trans_inv, Functor.isoWhiskerLeft_inv]
  congr 1
  unfold compactSupportDirectModel
  rw [pushforwardCongr_eq]
  rfl

private theorem scalarPull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (nativeScalarPull A (f ≫ g)).hom.app M ≫
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app M) =
    (StrictTower.moduleGComp (ULift.{u + 1} A) f g).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) f).map
        ((nativeScalarPull A g).hom.app M) ≫
      (nativeScalarPull A f).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).obj M) := by
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  have hd (N : Sheaf (ProEt.topology X) C) :
      (directForward A g).inv.app ((lowerStar C f).obj N) ≫
        (StrictTower.moduleDirectImage B g).map ((directForward A f).inv.app N) ≫
        (StrictTower.moduleRComp B f g).hom.app
          ((sfIntrinsicModuleEquivalence X A).functor.obj N) =
      (sfIntrinsicModuleEquivalence Z A).functor.map ((lowerStarComp C f g).hom.app N) ≫
        (directForward A (f ≫ g)).inv.app N := by
    apply (cancel_epi ((StrictTower.moduleDirectImage B g).map
      ((directForward A f).hom.app N) ≫
        (directForward A g).hom.app ((lowerStar C f).obj N))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [reassoc_of% (directForward_comp A f g N)]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hn : conjugateEquiv (proEtaleConstantRingAdjunction A (f ≫ g))
      ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
      (StrictTower.moduleGComp B f g).inv = (StrictTower.moduleRComp B f g).inv := by
    change conjugateEquiv _ _
      ((conjugateIsoEquiv _ _).symm (StrictTower.moduleRComp B f g).symm).hom = _
    exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply _)
  have ht := equivalenceAdjunctionComparison_compositor
    (sfIntrinsicModuleEquivalence Z A) (sfIntrinsicModuleEquivalence Y A)
    (sfIntrinsicModuleEquivalence X A)
    (upperStarLowerStarAdjunction C g) (upperStarLowerStarAdjunction C f)
    (upperStarLowerStarAdjunction C (f ≫ g))
    (proEtaleConstantRingAdjunction A g) (proEtaleConstantRingAdjunction A f)
    (proEtaleConstantRingAdjunction A (f ≫ g))
    (directForward A g).symm (directForward A f).symm (directForward A (f ≫ g)).symm
    (nativeScalarPull A g).symm
    (nativeScalarPull A f).symm
    (nativeScalarPull A (f ≫ g)).symm
    (directForward_mate A g) (directForward_mate A f) (directForward_mate A (f ≫ g))
    (lowerStarComp C f g) (StrictTower.moduleRComp B f g) hd
    (upperStarComp C f g).symm (StrictTower.moduleGComp B f g).symm
    (conjugateEquiv_upperStarComp_inv C f g) hn M
  have he :
      (sfIntrinsicModuleEquivalence X A).functor.mapIso
          ((upperStarComp C f g).symm.app M) ≪≫
        (nativeScalarPull A (f ≫ g)).symm.app M =
      (nativeScalarPull A f).symm.app ((upperStar C g).obj M) ≪≫
        (StrictTower.modulePullback B f).mapIso
          ((nativeScalarPull A g).symm.app M) ≪≫
        (StrictTower.moduleGComp B f g).symm.app
          ((sfIntrinsicModuleEquivalence Z A).functor.obj M) := Iso.ext ht
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
    Category.assoc] using congrArg Iso.inv he

private theorem cancelCoordinates_eq_inverse
    {C D Cn Dn : Type*} [Category C] [Category D] [Category Cn] [Category Dn]
    (e : C ≌ Cn) (f : D ≌ Dn) (L : C ⥤ D) (Ln : Cn ⥤ Dn)
    (s : e.functor ⋙ Ln ≅ L ⋙ f.functor)
    (q : Ln ≅ e.inverse ⋙ L ⋙ f.functor)
    (hq : q = (Functor.leftUnitor Ln).symm ≪≫
      Functor.isoWhiskerRight e.counitIso.symm Ln ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft e.inverse s) :
    cancelCoordinates e f L Ln q =
      IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison e f Ln L s := by
  subst q
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simp only [cancelCoordinates,
    IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.id_comp, Category.assoc]
  erw [Category.comp_id]

private theorem ordinaryPull_eq_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryPullCoordinates A f =
      IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
        (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence X A)
        (StrictTower.modulePullback (ULift.{u + 1} A) f)
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
        (nativeScalarPull A f) := by
  unfold nativeScalarPull
  exact cancelCoordinates_eq_inverse _ _ _ _ _ _
    (finiteIntrinsicOrdinaryPullbackNormalization A f)

private def OrdinaryPullSquare
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : Prop :=
  ∀ N : StrictTower.Modules (ULift.{u + 1} A) Z,
    (sfIntrinsicModuleEquivalence U A).inverse.map
        ((StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app N) ≫
      (ordinaryPullCoordinates A k).hom.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) p).obj N) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) k).map
        ((ordinaryPullCoordinates A p).hom.app N) =
    (ordinaryPullCoordinates A r).hom.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) i).obj N) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) r).map
        ((ordinaryPullCoordinates A i).hom.app N) ≫
      (upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app
        ((sfIntrinsicModuleEquivalence Z A).inverse.obj N)

private theorem scalarPull_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1} A)) h)).hom.app
        ((sfIntrinsicModuleEquivalence Y A).functor.obj M) ≫
      (nativeScalarPull A g).hom.app M =
    (nativeScalarPull A f).hom.app M ≫
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h).hom.app M) := by
  subst g
  simp [upperStarCongr]

private theorem iso_compositor_cancel {C : Type*} [Category C]
    {X Y Z T : C} (a : X ≅ Y) (d : X ≅ Z) (b : Z ≅ T)
    (σ : Y ≅ T) (hσ : σ = a.symm ≪≫ d ≪≫ b) :
    a.hom ≫ σ.hom = d.hom ≫ b.hom := by
  rw [hσ]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem native_square_compositor {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : StrictTower.Modules (ULift.{u + 1} A) Z) :
    (StrictTower.moduleGComp (ULift.{u + 1} A) r i).hom.app M ≫
        (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app M =
      (eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1} A)) h.symm)).hom.app M ≫
        (StrictTower.moduleGComp (ULift.{u + 1} A) k p).hom.app M := by
  have q := iso_compositor_cancel
    (StrictTower.moduleGComp (ULift.{u + 1} A) r i)
    (eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1} A)) h.symm))
    (StrictTower.moduleGComp (ULift.{u + 1} A) k p)
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h)
    (StrictTower.moduleSquareG_eq (ULift.{u + 1} A) k r p i h)
  exact congrArg (fun t ↦ t.app M) q

private theorem mapped_nat_iso_compositor_cancel
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) {P Q R S : C ⥤ D} (a : P ≅ Q) (d : P ≅ R) (b : R ≅ S)
    (σ : Q ≅ S) (hσ : σ = a.symm ≪≫ d ≪≫ b) (M : C) :
    F.map (a.hom.app M) ≫ F.map (σ.hom.app M) =
      F.map (d.hom.app M) ≫ F.map (b.hom.app M) := by
  have q := congrArg (fun t ↦ F.map (t.app M)) (iso_compositor_cancel a d b σ hσ)
  simpa only [NatTrans.comp_app, Functor.map_comp] using q

private theorem fixed_square_compositor {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) r i).hom.app M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M) =
    (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) k p).hom.app M) := by
  exact mapped_nat_iso_compositor_cancel (sfIntrinsicModuleEquivalence U A).functor
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) r i)
    (upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm)
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) k p)
    (upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm)
    (by unfold upperStarCompIso; rfl) M

private structure ScalarFrame (N : Type*) [Category N] where
  X₀ : N
  X₁ : N
  X₂ : N
  X₃ : N
  Y₀ : N
  Y₁ : N
  Y₂ : N
  Y₃ : N
  I₀ : N
  I₁ : N
  a : X₀ ⟶ X₁
  epi_a : Epi a
  b : X₂ ⟶ X₃
  d : X₀ ⟶ X₂
  s₀ : X₀ ⟶ Y₀
  s₂ : X₂ ⟶ Y₂
  c₀ : Y₀ ⟶ Y₁
  c₂ : Y₂ ⟶ Y₃
  q : Y₀ ⟶ Y₂
  t₀ : X₁ ⟶ I₀
  t₁ : I₀ ⟶ Y₁
  u₀ : X₃ ⟶ I₁
  u₁ : I₁ ⟶ Y₃
  σ : X₁ ⟶ X₃
  τ : Y₁ ⟶ Y₃

private def scalarLaw_hn {N : Type*} [Category N] (d : ScalarFrame N) : Prop :=
  d.a ≫ d.σ = d.d ≫ d.b

private def scalarLaw_hf {N : Type*} [Category N] (d : ScalarFrame N) : Prop :=
  d.c₀ ≫ d.τ = d.q ≫ d.c₂

private def scalarLaw_hi {N : Type*} [Category N] (d : ScalarFrame N) : Prop :=
  d.s₀ ≫ d.c₀ = d.a ≫ d.t₀ ≫ d.t₁

private def scalarLaw_hp {N : Type*} [Category N] (d : ScalarFrame N) : Prop :=
  d.s₂ ≫ d.c₂ = d.b ≫ d.u₀ ≫ d.u₁

private def scalarLaw_hc {N : Type*} [Category N] (d : ScalarFrame N) : Prop :=
  d.d ≫ d.s₂ = d.s₀ ≫ d.q

private structure ScalarRelations {N : Type*} [Category N] (d : ScalarFrame N) : Prop where
  hn : scalarLaw_hn d
  hf : scalarLaw_hf d
  hi : scalarLaw_hi d
  hp : scalarLaw_hp d
  hc : scalarLaw_hc d

private def scalarFrameData
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M)) :
    ScalarFrame (StrictTower.Modules (ULift.{u + 1} A) U) := by
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  let EZ := (sfIntrinsicModuleEquivalence Z A).functor
  let EU := (sfIntrinsicModuleEquivalence U A).functor
  exact {
    X₀ := (StrictTower.modulePullback B (r ≫ i)).obj (EZ.obj M)
    X₁ := (StrictTower.modulePullback B r).obj
      ((StrictTower.modulePullback B i).obj (EZ.obj M))
    X₂ := (StrictTower.modulePullback B (k ≫ p)).obj (EZ.obj M)
    X₃ := (StrictTower.modulePullback B k).obj
      ((StrictTower.modulePullback B p).obj (EZ.obj M))
    Y₀ := EU.obj ((upperStar C (r ≫ i)).obj M)
    Y₁ := EU.obj ((upperStar C r).obj ((upperStar C i).obj M))
    Y₂ := EU.obj ((upperStar C (k ≫ p)).obj M)
    Y₃ := EU.obj ((upperStar C k).obj ((upperStar C p).obj M))
    I₀ := (StrictTower.modulePullback B r).obj
      ((sfIntrinsicModuleEquivalence W A).functor.obj ((upperStar C i).obj M))
    I₁ := (StrictTower.modulePullback B k).obj
      ((sfIntrinsicModuleEquivalence V A).functor.obj ((upperStar C p).obj M))
    a := (StrictTower.moduleGComp B r i).hom.app (EZ.obj M)
    epi_a := inferInstance
    b := (StrictTower.moduleGComp B k p).hom.app (EZ.obj M)
    d := d
    s₀ := (nativeScalarPull A (r ≫ i)).hom.app M
    s₂ := (nativeScalarPull A (k ≫ p)).hom.app M
    c₀ := EU.map ((upperStarComp C r i).hom.app M)
    c₂ := EU.map ((upperStarComp C k p).hom.app M)
    q := EU.map ((upperStarCongr C h.symm).hom.app M)
    t₀ := (StrictTower.modulePullback B r).map ((nativeScalarPull A i).hom.app M)
    t₁ := (nativeScalarPull A r).hom.app ((upperStar C i).obj M)
    u₀ := (StrictTower.modulePullback B k).map ((nativeScalarPull A p).hom.app M)
    u₁ := (nativeScalarPull A k).hom.app ((upperStar C p).obj M)
    σ := (StrictTower.moduleSquareG B k r p i h).hom.app (EZ.obj M)
    τ := EU.map ((upperStarCompIso C h.symm).hom.app M)
  }

private theorem scalarFrame_hn
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hn : (StrictTower.moduleGComp (ULift.{u + 1} A) r i).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) =
      d ≫ (StrictTower.moduleGComp (ULift.{u + 1} A) k p).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M)) :
    scalarLaw_hn (scalarFrameData A k r p i h M d) := by
  native_exact hn

private theorem scalarFrame_hf
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M)) :
    scalarLaw_hf (scalarFrameData A k r p i h M d) := by
  native_exact fixed_square_compositor A k r p i h M

private theorem scalarFrame_hi
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M)) :
    scalarLaw_hi (scalarFrameData A k r p i h M d) := by
  native_exact scalarPull_comp A r i M

private theorem scalarFrame_hp
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M)) :
    scalarLaw_hp (scalarFrameData A k r p i h M d) := by
  native_exact scalarPull_comp A k p M

private theorem scalarFrame_hc
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hc : d ≫ (nativeScalarPull A (k ≫ p)).hom.app M =
      (nativeScalarPull A (r ≫ i)).hom.app M ≫
        (sfIntrinsicModuleEquivalence U A).functor.map
          ((upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    scalarLaw_hc (scalarFrameData A k r p i h M d) := by
  native_exact hc

private theorem scalarFrameRelations
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hn : (StrictTower.moduleGComp (ULift.{u + 1} A) r i).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) =
      d ≫ (StrictTower.moduleGComp (ULift.{u + 1} A) k p).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hc : d ≫ (nativeScalarPull A (k ≫ p)).hom.app M =
      (nativeScalarPull A (r ≫ i)).hom.app M ≫
        (sfIntrinsicModuleEquivalence U A).functor.map
          ((upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    ScalarRelations (scalarFrameData A k r p i h M d) := by
  exact {
    hn := scalarFrame_hn A k r p i h M d hn
    hf := scalarFrame_hf A k r p i h M d
    hi := scalarFrame_hi A k r p i h M d
    hp := scalarFrame_hp A k r p i h M d
    hc := scalarFrame_hc A k r p i h M d hc
  }

private theorem scalarPull_square_of_transport
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (d : (StrictTower.modulePullback (ULift.{u + 1} A) (r ≫ i)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ⟶
      (StrictTower.modulePullback (ULift.{u + 1} A) (k ≫ p)).obj
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hn : (StrictTower.moduleGComp (ULift.{u + 1} A) r i).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) =
      d ≫ (StrictTower.moduleGComp (ULift.{u + 1} A) k p).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (hc : d ≫ (nativeScalarPull A (k ≫ p)).hom.app M =
      (nativeScalarPull A (r ≫ i)).hom.app M ≫
        (sfIntrinsicModuleEquivalence U A).functor.map
          ((upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((nativeScalarPull A p).hom.app M) ≫
      (nativeScalarPull A k).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).obj M) =
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((nativeScalarPull A i).hom.app M) ≫
      (nativeScalarPull A r).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M) := by
  native_exact (scalarFrameRelations A k r p i h M d hn hc).result

private theorem scalarPull_square
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((nativeScalarPull A p).hom.app M) ≫
      (nativeScalarPull A k).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).obj M) =
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((nativeScalarPull A i).hom.app M) ≫
      (nativeScalarPull A r).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M) := by
  exact scalarPull_square_of_transport A k r p i h M
    ((eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1} A)) h.symm)).hom.app
      ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (native_square_compositor A k r p i h
      ((sfIntrinsicModuleEquivalence Z A).functor.obj M))
    (scalarPull_congr A h.symm M)

private structure PullSurface where
  Z : Cat.{vp, up}
  W : Cat.{vp, up}
  V : Cat.{vp, up}
  U : Cat.{vp, up}
  i : Z ⥤ W
  k : V ⥤ U
  p : Z ⥤ V
  r : W ⥤ U
  σ : i ⋙ r ≅ p ⋙ k

private structure PullCoordinates (n f : PullSurface.{vp, up}) where
  eZ : f.Z ≌ n.Z
  eW : f.W ≌ n.W
  eV : f.V ≌ n.V
  eU : f.U ≌ n.U
  si : eZ.functor ⋙ n.i ≅ f.i ⋙ eW.functor
  sk : eV.functor ⋙ n.k ≅ f.k ⋙ eU.functor
  sp : eZ.functor ⋙ n.p ≅ f.p ⋙ eV.functor
  sr : eW.functor ⋙ n.r ≅ f.r ⋙ eU.functor
  ci : n.i ⋙ eW.inverse ≅ eZ.inverse ⋙ f.i
  ck : n.k ⋙ eU.inverse ≅ eV.inverse ⋙ f.k
  cp : n.p ⋙ eV.inverse ≅ eZ.inverse ⋙ f.p
  cr : n.r ⋙ eU.inverse ≅ eW.inverse ⋙ f.r

private def pullLaw_h (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop :=
  ∀ M, n.σ.hom.app (c.eZ.functor.obj M) ≫
    n.k.map (c.sp.hom.app M) ≫ c.sk.hom.app (f.p.obj M) =
    n.r.map (c.si.hom.app M) ≫ c.sr.hom.app (f.i.obj M) ≫
      c.eU.functor.map (f.σ.hom.app M)

private def pullLaw_hi (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop :=
  c.ci = IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
    c.eZ c.eW n.i f.i c.si

private def pullLaw_hk (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop :=
  c.ck = IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
    c.eV c.eU n.k f.k c.sk

private def pullLaw_hp (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop :=
  c.cp = IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
    c.eZ c.eV n.p f.p c.sp

private def pullLaw_hr (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop :=
  c.cr = IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
    c.eW c.eU n.r f.r c.sr

private structure PullLaws (n f : PullSurface.{vp, up})
    (c : PullCoordinates n f) : Prop where
  h : pullLaw_h n f c
  hi : pullLaw_hi n f c
  hk : pullLaw_hk n f c
  hp : pullLaw_hp n f c
  hr : pullLaw_hr n f c

private def nativePullSurface
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : PullSurface.{u + 1, u + 2} :=
  let B := ULift.{u + 1} A
  { Z := Cat.of (StrictTower.Modules B Z)
    W := Cat.of (StrictTower.Modules B W)
    V := Cat.of (StrictTower.Modules B V)
    U := Cat.of (StrictTower.Modules B U)
    i := StrictTower.modulePullback B i
    k := StrictTower.modulePullback B k
    p := StrictTower.modulePullback B p
    r := StrictTower.modulePullback B r
    σ := StrictTower.moduleSquareG B k r p i h }

private def fixedPullSurface
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : PullSurface.{u + 1, u + 2} :=
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  { Z := Cat.of (Sheaf (ProEt.topology Z) C)
    W := Cat.of (Sheaf (ProEt.topology W) C)
    V := Cat.of (Sheaf (ProEt.topology V) C)
    U := Cat.of (Sheaf (ProEt.topology U) C)
    i := upperStar C i
    k := upperStar C k
    p := upperStar C p
    r := upperStar C r
    σ := upperStarCompIso C h.symm }

private def ordinaryPullCoordinatesData
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    PullCoordinates (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h) :=
  { eZ := sfIntrinsicModuleEquivalence Z A
    eW := sfIntrinsicModuleEquivalence W A
    eV := sfIntrinsicModuleEquivalence V A
    eU := sfIntrinsicModuleEquivalence U A
    si := nativeScalarPull A i
    sk := nativeScalarPull A k
    sp := nativeScalarPull A p
    sr := nativeScalarPull A r
    ci := ordinaryPullCoordinates A i
    ck := ordinaryPullCoordinates A k
    cp := ordinaryPullCoordinates A p
    cr := ordinaryPullCoordinates A r }

private theorem ordinaryPullLaw_h
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (hs : ∀ (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))),
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((nativeScalarPull A p).hom.app M) ≫
      (nativeScalarPull A k).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).obj M) =
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((nativeScalarPull A i).hom.app M) ≫
      (nativeScalarPull A r).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    pullLaw_h (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  native_exact hs

private theorem ordinaryPullLaw_hi
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pullLaw_hi (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  exact ordinaryPull_eq_inverse A i

private theorem ordinaryPullLaw_hk
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pullLaw_hk (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  exact ordinaryPull_eq_inverse A k

private theorem ordinaryPullLaw_hp
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pullLaw_hp (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  exact ordinaryPull_eq_inverse A p

private theorem ordinaryPullLaw_hr
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pullLaw_hr (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  exact ordinaryPull_eq_inverse A r

private theorem ordinaryPullLawsData
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (hs : ∀ (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))),
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((nativeScalarPull A p).hom.app M) ≫
      (nativeScalarPull A k).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).obj M) =
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((nativeScalarPull A i).hom.app M) ≫
      (nativeScalarPull A r).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    PullLaws (nativePullSurface A k r p i h) (fixedPullSurface A k r p i h)
      (ordinaryPullCoordinatesData A k r p i h) := by
  exact {
    h := ordinaryPullLaw_h A k r p i h hs
    hi := ordinaryPullLaw_hi A k r p i h
    hk := ordinaryPullLaw_hk A k r p i h
    hp := ordinaryPullLaw_hp A k r p i h
    hr := ordinaryPullLaw_hr A k r p i h
  }

private theorem ordinary_pull_square_of_forward
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i)
    (hs : ∀ (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} A))),
    (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((nativeScalarPull A p).hom.app M) ≫
      (nativeScalarPull A k).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).obj M) =
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((nativeScalarPull A i).hom.app M) ≫
      (nativeScalarPull A r).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj M) ≫
      (sfIntrinsicModuleEquivalence U A).functor.map
        ((upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) h.symm).hom.app M)) :
    OrdinaryPullSquare A k r p i h := by
  intro N
  native_exact (ordinaryPullLawsData A k r p i h hs).result N

private theorem ordinary_pull_square
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : OrdinaryPullSquare A k r p i h := by
  exact ordinary_pull_square_of_forward A k r p i h (scalarPull_square A k r p i h)

private theorem normalize_inverse_word
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Z T : D} (u : X ≅ Y)
    (a : F.obj Y ⟶ Z) (b : Z ⟶ T) (v : F.obj X ⟶ T)
    (h : a ≫ b = F.map u.inv ≫ v) : F.map u.hom ≫ a ≫ b = v := by
  rw [h, ← F.map_comp_assoc, u.hom_inv_id, F.map_id, Category.id_comp]

private theorem native_alpha_normalized
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Modules (ULift.{u + 1} A) W) :
    (StrictTower.modulePullback (ULift.{u + 1} A) r).map
        ((StrictTower.moduleJAdj (ULift.{u + 1} A) i).unit.app M) ≫
      (StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
        ((StrictTower.moduleJ (ULift.{u + 1} A) i).obj M) ≫
      (StrictTower.modulePullback (ULift.{u + 1} A) k).map
        ((StrictTower.singleAlpha (ULift.{u + 1} A) k r p i h).app M) =
      (StrictTower.moduleJAdj (ULift.{u + 1} A) k).unit.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) r).obj M) := by
  have := StrictTower.clopenModule_openUnit_isIso (ULift.{u + 1} A) i
  exact normalize_inverse_word (StrictTower.modulePullback (ULift.{u + 1} A) r)
    ((asIso (StrictTower.moduleJAdj (ULift.{u + 1} A) i).unit).app M)
    ((StrictTower.moduleSquareG (ULift.{u + 1} A) k r p i h).hom.app
      ((StrictTower.moduleJ (ULift.{u + 1} A) i).obj M))
    ((StrictTower.modulePullback (ULift.{u + 1} A) k).map
      ((StrictTower.singleAlpha (ULift.{u + 1} A) k r p i h).app M))
    ((StrictTower.moduleJAdj (ULift.{u + 1} A) k).unit.app
      ((StrictTower.modulePullback (ULift.{u + 1} A) r).obj M))
    (StrictTower.singleAlpha_restriction_normalized (ULift.{u + 1} A) k r p i h M)

private structure NormalSurface where
  A : Cat.{vf, uf}
  B : Cat.{vf, uf}
  C : Cat.{vf, uf}
  D : Cat.{vf, uf}
  I : A ⥤ B
  T : B ⥤ A
  P : B ⥤ C
  R : A ⥤ D
  J : D ⥤ C
  K : C ⥤ D
  ηI : 𝟭 A ⟶ I ⋙ T
  ηJ : 𝟭 D ⟶ J ⋙ K
  σ : T ⋙ R ≅ P ⋙ K
  α : I ⋙ P ⟶ R ⋙ J

private structure NormalCoordinates (n f : NormalSurface.{vf, uf}) where
  uA : n.A ⥤ f.A
  uB : n.B ⥤ f.B
  uC : n.C ⥤ f.C
  uD : n.D ⥤ f.D
  cI : n.I ⋙ uB ≅ uA ⋙ f.I
  cT : n.T ⋙ uA ≅ uB ⋙ f.T
  cP : n.P ⋙ uC ≅ uB ⋙ f.P
  cR : n.R ⋙ uD ≅ uA ⋙ f.R
  cJ : n.J ⋙ uC ≅ uD ⋙ f.J
  cK : n.K ⋙ uD ≅ uC ⋙ f.K

private def normalLaw_huI (n f : NormalSurface.{vf, uf})
    (c : NormalCoordinates n f) : Prop :=
  ∀ M, c.uA.map (n.ηI.app M) ≫ c.cT.hom.app (n.I.obj M) ≫
    f.T.map (c.cI.hom.app M) = f.ηI.app (c.uA.obj M)

private def normalLaw_huJ (n f : NormalSurface.{vf, uf})
    (c : NormalCoordinates n f) : Prop :=
  ∀ N, c.uD.map (n.ηJ.app N) ≫ c.cK.hom.app (n.J.obj N) ≫
    f.K.map (c.cJ.hom.app N) = f.ηJ.app (c.uD.obj N)

private def normalLaw_hs (n f : NormalSurface.{vf, uf})
    (c : NormalCoordinates n f) : Prop :=
  ∀ N, c.uD.map (n.σ.hom.app N) ≫ c.cK.hom.app (n.P.obj N) ≫
    f.K.map (c.cP.hom.app N) = c.cR.hom.app (n.T.obj N) ≫
      f.R.map (c.cT.hom.app N) ≫ f.σ.hom.app (c.uB.obj N)

private def normalLaw_hn (n f : NormalSurface.{vf, uf})
    (_c : NormalCoordinates n f) : Prop :=
  ∀ M, n.R.map (n.ηI.app M) ≫ n.σ.hom.app (n.I.obj M) ≫
    n.K.map (n.α.app M) = n.ηJ.app (n.R.obj M)

private def normalLaw_hnFixed (n f : NormalSurface.{vf, uf})
    (_c : NormalCoordinates n f) : Prop :=
  ∀ M, f.R.map (f.ηI.app M) ≫ f.σ.hom.app (f.I.obj M) ≫
    f.K.map (f.α.app M) = f.ηJ.app (f.R.obj M)

private def normalLaw_hinj (n f : NormalSurface.{vf, uf})
    (_c : NormalCoordinates n f) : Prop :=
  ∀ (X : f.C) (Y : f.D) (a b : X ⟶ f.J.obj Y),
    f.K.map a = f.K.map b → a = b

private def normalLaw_isoηI (n f : NormalSurface.{vf, uf})
    (_c : NormalCoordinates n f) : Prop :=
  IsIso n.ηI

private structure NormalLaws (n f : NormalSurface.{vf, uf})
    (c : NormalCoordinates n f) : Prop where
  isoηI : normalLaw_isoηI n f c
  huI : normalLaw_huI n f c
  huJ : normalLaw_huJ n f c
  hs : normalLaw_hs n f c
  hn : normalLaw_hn n f c
  hn' : normalLaw_hnFixed n f c
  hinj : normalLaw_hinj n f c

private def nativeNormalSurface
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) : NormalSurface.{u + 1, u + 2} :=
  let B := ULift.{u + 1} A
  { A := Cat.of (StrictTower.Modules B W)
    B := Cat.of (StrictTower.Modules B Z)
    C := Cat.of (StrictTower.Modules B V)
    D := Cat.of (StrictTower.Modules B U)
    I := StrictTower.moduleJ B i
    T := StrictTower.modulePullback B i
    P := StrictTower.modulePullback B p
    R := StrictTower.modulePullback B r
    J := StrictTower.moduleJ B k
    K := StrictTower.modulePullback B k
    ηI := (StrictTower.moduleJAdj B i).unit
    ηJ := (StrictTower.moduleJAdj B k).unit
    σ := StrictTower.moduleSquareG B k r p i h
    α := StrictTower.singleAlpha B k r p i h }

private def fixedNormalSurface
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) : NormalSurface.{u + 1, u + 2} :=
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  { A := Cat.of (Sheaf (ProEt.topology W) C)
    B := Cat.of (Sheaf (ProEt.topology Z) C)
    C := Cat.of (Sheaf (ProEt.topology V) C)
    D := Cat.of (Sheaf (ProEt.topology U) C)
    I := openImmersionLowerShriek C i
    T := upperStar C i
    P := upperStar C p
    R := upperStar C r
    J := openImmersionLowerShriek C k
    K := upperStar C k
    ηI := (openImmersionLowerShriekUpperStarAdjunction C i).unit
    ηJ := (openImmersionLowerShriekUpperStarAdjunction C k).unit
    σ := upperStarCompIso C h.symm
    α := AmbientClopen.alpha B k r p i h }

private def ordinaryNormalCoordinates
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    NormalCoordinates (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h) :=
  { uA := (sfIntrinsicModuleEquivalence W A).inverse
    uB := (sfIntrinsicModuleEquivalence Z A).inverse
    uC := (sfIntrinsicModuleEquivalence V A).inverse
    uD := (sfIntrinsicModuleEquivalence U A).inverse
    cI := ordinaryShriekCoordinates A i
    cT := ordinaryPullCoordinates A i
    cP := ordinaryPullCoordinates A p
    cR := ordinaryPullCoordinates A r
    cJ := ordinaryShriekCoordinates A k
    cK := ordinaryPullCoordinates A k }

private theorem ordinary_normalLaw_huI
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_huI (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  intro M
  exact ordinary_open_unit A i M

private theorem ordinary_normalLaw_huJ
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_huJ (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  intro M
  exact ordinary_open_unit A k M

private theorem ordinary_normalLaw_hs
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (hs : OrdinaryPullSquare A k r p i h) :
    normalLaw_hs (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  native_exact hs

private theorem ordinary_normalLaw_hn
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_hn (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  intro M
  exact native_alpha_normalized A k r p i h M

private theorem ordinary_normalLaw_hnFixed
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_hnFixed (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  intro M
  native_exact AmbientClopen.ordinary_alpha_normalized (ULift.{u + 1} A) k r p i h M

private theorem ordinary_normalLaw_hinj
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_hinj (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  unfold normalLaw_hinj
  change ∀ (X : Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (Y : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (a b : X ⟶ (openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) k).obj Y),
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) k).map a =
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) k).map b → a = b
  intro X Y a b hab
  have := mono_upperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
    k (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y
  exact AmbientClopen.unit_map_injective
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) k) hab

private theorem ordinary_normalLaw_isoηI
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    normalLaw_isoηI (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  exact StrictTower.clopenModule_openUnit_isIso (ULift.{u + 1} A) i

private theorem ordinaryNormalLaws
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (hs : OrdinaryPullSquare A k r p i h) :
    NormalLaws (nativeNormalSurface A k r p i h) (fixedNormalSurface A k r p i h)
      (ordinaryNormalCoordinates A k r p i h) := by
  exact {
    isoηI := ordinary_normalLaw_isoηI A k r p i h
    huI := ordinary_normalLaw_huI A k r p i h
    huJ := ordinary_normalLaw_huJ A k r p i h
    hs := ordinary_normalLaw_hs A k r p i h hs
    hn := ordinary_normalLaw_hn A k r p i h
    hn' := ordinary_normalLaw_hnFixed A k r p i h
    hinj := ordinary_normalLaw_hinj A k r p i h
  }

private theorem ordinary_alpha_of_square
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (hs : OrdinaryPullSquare A k r p i h)
    (M : StrictTower.Modules (ULift.{u + 1} A) W) :
    (sfIntrinsicModuleEquivalence V A).inverse.map
        ((StrictTower.singleAlpha (ULift.{u + 1} A) k r p i h).app M) ≫
      (ordinaryShriekCoordinates A k).hom.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) r).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) k).map
        ((ordinaryPullCoordinates A r).hom.app M) =
    (ordinaryPullCoordinates A p).hom.app
        ((StrictTower.moduleJ (ULift.{u + 1} A) i).obj M) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).map
        ((ordinaryShriekCoordinates A i).hom.app M) ≫
      (AmbientClopen.alpha (ULift.{u + 1} A) k r p i h).app
        ((sfIntrinsicModuleEquivalence W A).inverse.obj M) := by
  exact (ordinaryNormalLaws A k r p i h hs).result M

private theorem localized_inverseComparison
    {C D Cn Dn : Type*} [Category C] [Category D] [Category Cn] [Category Dn]
    [Abelian C] [Abelian D] [Abelian Cn] [Abelian Dn]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory Cn] [HasDerivedCategory Dn]
    (e : C ≌ Cn) (f : D ≌ Dn) (L : C ⥤ D) (Ln : Cn ⥤ Dn)
    [e.functor.Additive] [e.inverse.Additive] [f.functor.Additive] [f.inverse.Additive]
    [L.Additive] [Ln.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits Ln] [PreservesFiniteColimits Ln]
    (s : e.functor ⋙ Ln ≅ L ⋙ f.functor) :
    (Functor.mapDerivedCategorySquareIso
      (IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison e f Ln L s)).hom =
    (IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
      e.mapDerivedCategory f.mapDerivedCategory Ln.mapDerivedCategory L.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso s)).hom := by
  let δ := IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison e f Ln L s
  generalize hsd : Functor.mapDerivedCategorySquareIso s = sd
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso Cn (.up ℤ))
  intro K
  let T := (L.mapHomologicalComplex (.up ℤ)).obj
    ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)
  let a := L.mapDerivedCategory.map (e.inverse.mapDerivedCategoryFactors.hom.app K) ≫
    L.mapDerivedCategoryFactors.hom.app ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)
  have hs := sd.hom.naturality (e.inverse.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs
  have hsK := Functor.exactSquare_fac s
    ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)
  rw [hsd] at hsK
  have ho : sd.hom.app (e.inverse.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      f.functor.mapDerivedCategory.map a ≫
      f.functor.mapDerivedCategoryFactors.hom.app T =
      Ln.mapDerivedCategory.map
          (e.functor.mapDerivedCategory.map (e.inverse.mapDerivedCategoryFactors.hom.app K)) ≫
        Ln.mapDerivedCategory.map (e.functor.mapDerivedCategoryFactors.hom.app
          ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        Ln.mapDerivedCategoryFactors.hom.app
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj
            ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
          ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)) := by
    dsimp only [a, T]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hs, hsK]
  have hc : e.mapDerivedCategory.counitIso.inv.app (DerivedCategory.Q.obj K) ≫
      e.functor.mapDerivedCategory.map (e.inverse.mapDerivedCategoryFactors.hom.app K) ≫
      e.functor.mapDerivedCategoryFactors.hom.app
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.counitIso.inv (.up ℤ)).app K) := by
    have : IsIso ((NatTrans.mapHomologicalComplex e.counitIso.hom (.up ℤ)).app K) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex e.counitIso (.up ℤ)).hom.app K))
    apply (cancel_mono (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e.counitIso.hom (.up ℤ)).app K))).mp
    rw [Category.assoc, Category.assoc, Functor.derived_counit_factors]
    simp only [Iso.inv_hom_id_app, ← Functor.map_comp]
    have hi : (NatTrans.mapHomologicalComplex e.counitIso.inv (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex e.counitIso.hom (.up ℤ)).app K = 𝟙 _ := by
      ext n
      exact e.counitIso.inv_hom_id_app (K.X n)
    rw [hi, CategoryTheory.Functor.map_id]
    rfl
  apply (cancel_mono a).mp
  rw [Functor.exactSquare_fac δ K]
  simp only [IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Category.assoc]
  have hu := f.mapDerivedCategory.unitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu ⊢
  erw [← hu]
  rw [← Functor.derived_unitInv_factors f T]
  slice_rhs 2 4 =>
    erw [← f.inverse.mapDerivedCategory.map_comp, ← f.inverse.mapDerivedCategory.map_comp]
  erw [ho]
  simp only [Category.assoc]
  erw [← f.inverse.mapDerivedCategory.map_comp_assoc]
  simp only [← Ln.mapDerivedCategory.map_comp_assoc]
  rw [hc]
  erw [Ln.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  rw [f.inverse.mapDerivedCategory.map_comp, Category.assoc]
  erw [f.inverse.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  congr 2
  congr 1
  ext n
  simp only [δ, IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.map_comp, Category.assoc]
  rfl

private theorem ordinaryShriek_eq_inverse {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    ordinaryShriekCoordinates A j =
      Functor.isoWhiskerRight (compactSupportOpenModel j A)
          (sfIntrinsicModuleEquivalence Y A).inverse ≪≫
        IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison
          (sfIntrinsicModuleEquivalence X A) (sfIntrinsicModuleEquivalence Y A)
          (sfIntrinsicExtensionByZero j A)
          (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
          (sfIntrinsicOpenExtensionComparison A j) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simp only [ordinaryShriekCoordinates, cancelCoordinates,
    IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison,
    sfIntrinsicOpenExtensionComparison, sfIntrinsicExtensionByZero,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app, Functor.comp_map,
    Category.id_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    ← Equivalence.unit_app_inverse, Equivalence.unit, Iso.hom_inv_id_app,
    ]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.id_comp]

private theorem derived_square_precomp
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {P P' : C ⥤ D} {U : D ⥤ F} {V : C ⥤ E} {Q : E ⥤ F}
    [P.Additive] [P'.Additive] [U.Additive] [V.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (z : P ≅ P') (q : P' ⋙ U ≅ V ⋙ Q) :
    (Functor.mapDerivedCategorySquareIso (Functor.isoWhiskerRight z U ≪≫ q)).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso z).hom U.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso q).hom := by
  have hz := Functor.mapDerivedCategoryNatIso_isoWhiskerRight z U
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso P U).hom).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hz, Iso.hom_inv_id_assoc]

/-- Cancel the intrinsic coefficient presentation after the native inverse image.
Source: Stacks 00YV and 03DI; coefficient step of the finite alpha comparison.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
def finiteNativePullCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (StrictTower.modulePullback (ULift.{u + 1} A) f).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence X A).inverse ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙ ProperOpenPull (ULift.{u + 1} A) f :=
  Functor.mapDerivedCategorySquareIso
    (Functor.isoWhiskerRight (openSquarePullbackModel A f)
        (sfIntrinsicModuleEquivalence X A).inverse ≪≫
      Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).inverse
        (Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
          (sfIntrinsicModuleEquivalence X A).unitIso.symm) ≪≫
      Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).inverse
        (Functor.rightUnitor _)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence Y A).inverse
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- Cancel the intrinsic coefficient presentation after native extension by zero.
Source: Stacks 00YV and 03DI; coefficient step of the finite alpha comparison.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
def finiteNativeShriekCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (StrictTower.moduleJ (ULift.{u + 1} A) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙ ProperOpenShriek (ULift.{u + 1} A) j :=
  Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (compactSupportOpenModel j A))
      (sfIntrinsicDerivedEquivalence Y A).inverse ≪≫
    (let R := sfIntrinsicDerivedEquivalence X A
     let S := sfIntrinsicDerivedEquivalence Y A
     let F := ProperOpenShriek (ULift.{u + 1} A) j
     let G := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
     let q := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
       Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A j) ≪≫
         Functor.mapDerivedCategoryCompIso _ _
     (Functor.leftUnitor _).symm ≪≫
       Functor.isoWhiskerRight R.counitIso.symm (G ⋙ S.inverse) ≪≫
       Functor.associator _ _ _ ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _).symm ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerRight q S.inverse) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerLeft F S.unitIso.symm) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.rightUnitor F))

private theorem shriek_coordinates_localized {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (finiteNativeShriekCoordinates A j).hom =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := StrictTower.moduleJ (ULift.{u + 1} A) j)
        (F₂ := (sfIntrinsicModuleEquivalence Y A).inverse)
        (G₁ := (sfIntrinsicModuleEquivalence X A).inverse)
        (G₂ := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
        (ordinaryShriekCoordinates A j)).hom := by
  rw [ordinaryShriek_eq_inverse, derived_square_precomp, localized_inverseComparison]
  apply NatTrans.ext
  funext M
  simp only [finiteNativeShriekCoordinates,
    IntegralProjectionReduction.FiniteIntrinsicRealization.inverseComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp]
  dsimp only [sfIntrinsicDerivedEquivalence, ProperOpenShriek]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj]
  erw [Category.comp_id]
  rfl

private theorem pull_coordinates_localized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) Y)) :
    (finiteNativePullCoordinates A f).hom.app M =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := StrictTower.modulePullback (ULift.{u + 1} A) f)
        (F₂ := (sfIntrinsicModuleEquivalence X A).inverse)
        (G₁ := (sfIntrinsicModuleEquivalence Y A).inverse)
        (G₂ := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
        (ordinaryPullCoordinates A f)).hom.app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).inv.app
          ((sfIntrinsicDerivedEquivalence Y A).inverse.obj M) := by
  unfold finiteNativePullCoordinates ordinaryPullCoordinates cancelCoordinates
  rfl

private theorem exactSquare_eq_localizeSquare
    {C B : Type v₁} {D E : Type v₂}
    [Category.{h₁} C] [Category.{h₂} D] [Category.{h₁} B] [Category.{h₂} E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ B) (I : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (a : F ⋙ G ⟶ H ⋙ I) :
    StrictTower.MateEvaluationScalars.exactSquare F G H I a =
      AmbientClopen.localizeSquare F G H I a := by
  rfl

private theorem singleDerivedAlpha_eq_exactSquare
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    StrictTower.MateEvaluationScalars.singleDerivedAlpha (ULift.{u + 1} A) k r p i h =
      StrictTower.MateEvaluationScalars.exactSquare
        (StrictTower.moduleJ (ULift.{u + 1} A) i)
        (StrictTower.modulePullback (ULift.{u + 1} A) p)
        (StrictTower.modulePullback (ULift.{u + 1} A) r)
        (StrictTower.moduleJ (ULift.{u + 1} A) k)
        (StrictTower.singleAlpha (ULift.{u + 1} A) k r p i h) := by
  rfl

private theorem exactSquare_equivalences
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {F : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D}
    {F' : A' ⥤ B'} {G' : A' ⥤ C'} {H' : B' ⥤ D'} {K' : C' ⥤ D'}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [F'.Additive] [G'.Additive] [H'.Additive] [K'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (e₀ : A' ≌ A) (e₁ : B' ≌ B) (e₂ : C' ≌ C) (e₃ : D' ≌ D)
    [e₀.functor.Additive] [e₁.functor.Additive]
    [e₂.functor.Additive] [e₃.functor.Additive]
    [(e₀.inverse).Additive] [(e₁.inverse).Additive] [(e₂.inverse).Additive] [(e₃.inverse).Additive]
    [PreservesFiniteLimits (e₀.inverse)] [PreservesFiniteColimits (e₀.inverse)]
    [PreservesFiniteLimits (e₁.inverse)] [PreservesFiniteColimits (e₁.inverse)]
    [PreservesFiniteLimits (e₂.inverse)] [PreservesFiniteColimits (e₂.inverse)]
    [PreservesFiniteLimits (e₃.inverse)] [PreservesFiniteColimits (e₃.inverse)]
    (pF : F ⋙ (e₁.inverse) ≅ (e₀.inverse) ⋙ F') (pG : G ⋙ (e₂.inverse) ≅ (e₀.inverse) ⋙ G')
    (pH : H ⋙ (e₃.inverse) ≅ (e₁.inverse) ⋙ H') (pK : K ⋙ (e₃.inverse) ≅ (e₂.inverse) ⋙ K')
    (t : G ⋙ K ⟶ F ⋙ H) (t' : G' ⋙ K' ⟶ F' ⋙ H')
    (h : ∀ L, (e₃.inverse).map (t.app L) ≫ pH.hom.app (F.obj L) ≫ H'.map (pF.hom.app L) =
      pK.hom.app (G.obj L) ≫ K'.map (pG.hom.app L) ≫ t'.app ((e₀.inverse).obj L))
    (M : DerivedCategory A) :
    e₃.mapDerivedCategory.inverse.map
        ((StrictTower.MateEvaluationScalars.exactSquare G K F H t).app M) ≫
        (Functor.mapDerivedCategorySquareIso pH).hom.app (F.mapDerivedCategory.obj M) ≫
        H'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pF).hom.app M) =
      (Functor.mapDerivedCategorySquareIso pK).hom.app (G.mapDerivedCategory.obj M) ≫
        K'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pG).hom.app M) ≫
        (StrictTower.MateEvaluationScalars.exactSquare G' K' F' H' t').app
          (e₀.mapDerivedCategory.inverse.obj M) := by
  exact StrictTower.MateEvaluationScalars.exactSquare_scalar
    (A := A) (B := B) (C := C) (D := D)
    (A' := A') (B' := B') (C' := C') (D' := D')
    (F := F) (G := G) (H := H) (K := K)
    (F' := F') (G' := G') (H' := H') (K' := K')
    e₀.inverse e₁.inverse e₂.inverse e₃.inverse pF pG pH pK t t' h M

private def OrdinaryLocalizedAlphaSquare
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) W)) : Prop :=
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  (sfIntrinsicDerivedEquivalence V A).inverse.map
      ((StrictTower.MateEvaluationScalars.exactSquare
        (StrictTower.moduleJ B i) (StrictTower.modulePullback B p)
        (StrictTower.modulePullback B r) (StrictTower.moduleJ B k)
        (StrictTower.singleAlpha B k r p i h)).app M) ≫
    (Functor.mapDerivedCategorySquareIso (ordinaryShriekCoordinates A k)).hom.app
      ((StrictTower.modulePullback B r).mapDerivedCategory.obj M) ≫
    (openImmersionLowerShriek C k).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso (ordinaryPullCoordinates A r)).hom.app M) =
  (Functor.mapDerivedCategorySquareIso (ordinaryPullCoordinates A p)).hom.app
      ((StrictTower.moduleJ B i).mapDerivedCategory.obj M) ≫
    (upperStar C p).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso (ordinaryShriekCoordinates A i)).hom.app M) ≫
    (StrictTower.MateEvaluationScalars.exactSquare
      (openImmersionLowerShriek C i) (upperStar C p)
      (upperStar C r) (openImmersionLowerShriek C k)
      (AmbientClopen.alpha B k r p i h)).app
        ((sfIntrinsicDerivedEquivalence W A).inverse.obj M)

private theorem ordinary_alpha_derived
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) W)) :
    OrdinaryLocalizedAlphaSquare A k r p i h M := by
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  have ho := ordinary_alpha_of_square A k r p i h (ordinary_pull_square A k r p i h)
  have hd := exactSquare_equivalences
    (A := StrictTower.Modules B W) (B := StrictTower.Modules B U)
    (C := StrictTower.Modules B Z) (D := StrictTower.Modules B V)
    (A' := Sheaf (ProEt.topology W) C) (B' := Sheaf (ProEt.topology U) C)
    (C' := Sheaf (ProEt.topology Z) C) (D' := Sheaf (ProEt.topology V) C)
    (F := StrictTower.modulePullback B r) (G := StrictTower.moduleJ B i)
    (H := StrictTower.moduleJ B k) (K := StrictTower.modulePullback B p)
    (F' := upperStar C r) (G' := openImmersionLowerShriek C i)
    (H' := openImmersionLowerShriek C k) (K' := upperStar C p)
    (sfIntrinsicModuleEquivalence W A) (sfIntrinsicModuleEquivalence U A)
    (sfIntrinsicModuleEquivalence Z A) (sfIntrinsicModuleEquivalence V A)
    (ordinaryPullCoordinates A r) (ordinaryShriekCoordinates A i)
    (ordinaryShriekCoordinates A k) (ordinaryPullCoordinates A p)
    (StrictTower.singleAlpha B k r p i h) (AmbientClopen.alpha B k r p i h)
    (fun L ↦ by native_exact ho L) M
  exact hd

/-- The single-coefficient clopen alpha in its fixed sheaf presentation.

Source: Stacks 00YV, 03DI and 0F7B; the coefficient-equivalence step of
lem-sf-system-finite-alpha-coordinates.
Proof: before localization, both pull comparisons are inverse mates of the
section-preserving direct comparisons. Both open comparisons are their inverse
open mates. The cartesian beta therefore has the same open transpose in the two
presentations. The coefficient equivalence preserves the identity on the clopen
component and zero on its complement, so preserves the projector. Its unit and
counit identify the pull and open compositors. Paste these identities in the
ordinary alpha word. Apply the exact cochain functors and localization, inserting
the standard composition isomorphisms. The total-to-exact pull comparisons give
properOpenAlpha by ordinary_alpha_localized. Naturality and the equivalence
triangle identities give exactly the displayed inverse-coordinate formula.
Empty components and the zero ring use the same identity/zero calculation.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
theorem finiteNativeAlphaCoordinates
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) W)) :
    (sfIntrinsicDerivedEquivalence V A).inverse.map
        ((StrictTower.MateEvaluationScalars.singleDerivedAlpha
          (ULift.{u + 1} A) k r p i h).app M) ≫
      (finiteNativeShriekCoordinates A k).hom.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) r).mapDerivedCategory.obj M) ≫
      (ProperOpenShriek (ULift.{u + 1} A) k).map
        ((finiteNativePullCoordinates A r).hom.app M) =
    (finiteNativePullCoordinates A p).hom.app
        ((StrictTower.moduleJ (ULift.{u + 1} A) i).mapDerivedCategory.obj M) ≫
      (ProperOpenPull (ULift.{u + 1} A) p).map
        ((finiteNativeShriekCoordinates A i).hom.app M) ≫
      (properOpenAlpha (ULift.{u + 1} A) k r p i h).app
        ((sfIntrinsicDerivedEquivalence W A).inverse.obj M) := by
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  have hd := ordinary_alpha_derived A k r p i h M
  dsimp only [OrdinaryLocalizedAlphaSquare] at hd
  rw [← AmbientClopen.ordinary_alpha_localized B k r p i h]
  dsimp only [sfIntrinsicDerivedEquivalence, ProperOpenShriek] at hd ⊢
  simp only [AmbientClopen.derivedAlpha, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    pull_coordinates_localized, shriek_coordinates_localized,
    sfIntrinsicDerivedEquivalence, ProperOpenShriek, ProperOpenPull,
    Functor.map_comp, Category.assoc]
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory C p).inv.naturality_assoc]
  dsimp only [Functor.comp_obj]
  erw [Iso.inv_hom_id_app_assoc]
  have hf := congrArg
    (fun z ↦ z ≫ (openImmersionLowerShriek C k).mapDerivedCategory.map
      ((leftDerivedUpperStarIsoMapDerivedCategory C r).inv.app
        ((sfIntrinsicModuleEquivalence W A).mapDerivedCategory.inverse.obj M))) hd
  dsimp only [B, C] at hf ⊢
  rw [singleDerivedAlpha_eq_exactSquare, ← exactSquare_eq_localizeSquare]
  simp only [Category.assoc] at hf
  -- Compare the two derived-equivalence presentations after the diagram calculation.
  exact hf

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
