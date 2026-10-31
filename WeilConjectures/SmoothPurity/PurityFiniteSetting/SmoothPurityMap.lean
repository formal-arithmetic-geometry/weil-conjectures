/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-! # The specified finite-coefficient smooth purity map

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
def-pur-smooth-purity-map; master snapshot order 2012
(blueprint: def-pur-smooth-purity-map).

All arrows are constructed from the recorded diagonal orientation and tensor counit mate.
The original pro-etale coefficient K is retained. An etale representative and its
isomorphism are coordinates for the comparison, not choices of purity isomorphisms.
The exceptional target is the actual transported exceptional inverse image of K.
The shifted coefficient line is the recorded diagonalTwist; inverse shift provides its
unshifted presentation, so reassociation uses the ordinary tensor-shift comparison.

## Main definitions

* `smoothPurityTheta`: the canonical tensor counit mate in comparison coordinates.
* `smoothPurityReassociation`: canonical second-variable shift compatibility.
* `smoothPurityTensorMap`: the tensor form on the original intrinsic object.
* `smoothPurityMap`: its precomposition with twist reassociation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v uC
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the recorded positive quotient, without a ramification restriction.
Source: blueprint finite coefficient conventions (blueprint: def-pur-smooth-purity-map). -/
instance smoothPurityRingFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The recorded finite exceptional functor at the specified compactification.
Source: blueprint finite exceptional inverse image
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptional (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) ⥤
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor ⋙
    Etale.rightDerivedUpperShriek P.Coefficient f ⋙
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory

/-- The functor identity expressing the recorded finite exceptional transport.
Source: blueprint finite exceptional inverse image (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptionalComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.smoothPurityExceptional f ≅
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor ⋙
      Etale.rightDerivedUpperShriek P.Coefficient f ⋙
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory :=
  Iso.refl _

/-- Pullback of the original pro-etale object, in exact fixed-scalar coordinates.
Source: blueprint def-pur-smooth-purity-map, M = Lf* K
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) := ProEtale.sfFixedDerivedPullback P.Ring f

/-- The recorded tensor bifunctor with the fixed module-category instances cached.
Source: blueprint derived tensor product (blueprint: def-pur-smooth-purity-map). -/
@[implicit_reducible]
def smoothPurityTensor (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} A) X

/-- The degree-zero constant coefficient is the derived tensor unit.
Source: blueprint finite coefficient unit (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityUnitIso (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    Etale.ordinaryFiniteUnit A Y ≅
      𝟙_ (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y

/-- The canonical ordinary tensor mate, including the degree-zero unit comparison.
Source: blueprint def-pur-co-smoothness clause 2
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityEtaleTheta (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.ordinaryFinitePullback A f).obj K₀)).obj
        ((Etale.rightDerivedUpperShriek A f).obj
          (Etale.ordinaryFiniteUnit A Y)) ⟶
      (Etale.rightDerivedUpperShriek A f).obj K₀ :=
  ((Etale.ordinaryFiniteTensor A X).obj
    ((Etale.ordinaryFinitePullback A f).obj K₀)).map
      ((Etale.rightDerivedUpperShriek A f).map
        (smoothPurityUnitIso A Y).hom) ≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
      ((Etale.ordinaryFinitePullback A f).obj K₀)).app
        (Etale.dualizingComplex A f) ≫
    Etale.dualizingComplexTensorMap A f K₀

private theorem etaleTheta_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (g : K ⟶ K') :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj (Etale.dualizingComplex A f)).map
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map g) ≫
        Etale.dualizingComplexTensorMap A f K' =
      Etale.dualizingComplexTensorMap A f K ≫
        (Etale.rightDerivedUpperShriek A f).map g := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  have h := Adjunction.projectionTensorMap_naturality_right
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (fun M N ↦ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app M).app N)
    (Etale.projectionMap_app_app_naturality_right f) (𝟙_ _) g
  dsimp only [Etale.dualizingComplexTensorMap,
    Etale.lowerShriekRightAdjointUnitTensorMap]
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ _ ≫ (Etale.rightDerivedUpperShriek A f).map k)
    (leftUnitor_naturality g)

private theorem smoothPurityEtaleTheta_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (g : K ⟶ K') :
    ((Etale.ordinaryFiniteTensor A X).map ((Etale.ordinaryFinitePullback A f).map g)).app
        ((Etale.rightDerivedUpperShriek A f).obj
          (Etale.ordinaryFiniteUnit A Y)) ≫ smoothPurityEtaleTheta A f K' =
      smoothPurityEtaleTheta A f K ≫
        (Etale.rightDerivedUpperShriek A f).map g := by
  have hu := ((Etale.ordinaryFiniteTensor A X).map
    ((Etale.ordinaryFinitePullback A f).map g)).naturality
      ((Etale.rightDerivedUpperShriek A f).map
        (smoothPurityUnitIso A Y).hom)
  have hs := NatTrans.congr_app
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality
      ((Etale.ordinaryFinitePullback A f).map g))
    (Etale.dualizingComplex A f)
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app, NatTrans.comp_app,
    Functor.comp_map] at hs
  dsimp only [smoothPurityEtaleTheta]
  simp only [← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  erw [reassoc_of% hs, etaleTheta_naturality]

/-- Canonical pullback comparison at a representing isomorphism.
Source: blueprint def-pur-smooth-purity-map, M (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityPullbackComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    (P.smoothPurityPullback f).obj K ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₀) :=
  (P.smoothPurityPullback f).mapIso e.symm ≪≫
    (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).app K₀ ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).app K₀).symm

private theorem pullbackComparison_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    {K₀ K₁ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (e₀ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e₁ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₁ ≅ K)
    (g : K₀ ⟶ K₁)
    (hg : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g ≫ e₁.hom = e₀.hom) :
    (P.smoothPurityPullbackComparison f K K₀ e₀).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            ((Etale.ordinaryFinitePullback P.Coefficient f).map g) =
      (P.smoothPurityPullbackComparison f K K₁ e₁).hom := by
  have he : e₀.inv ≫ (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g = e₁.inv := by
    rw [← cancel_mono e₁.hom]
    simp [hg]
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let t := ProEtale.sfDerivedComparisonPullbackIso P.Ring f ≪≫
    Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f).symm F
  have ht := t.hom.naturality g
  change (P.smoothPurityPullback f).map
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g) ≫
      t.hom.app K₁ = t.hom.app K₀ ≫
        F.map ((Etale.ordinaryFinitePullback P.Coefficient f).map g) at ht
  have hfinal : (P.smoothPurityPullback f).map e₀.inv ≫ t.hom.app K₀ ≫
      F.map ((Etale.ordinaryFinitePullback P.Coefficient f).map g) =
      (P.smoothPurityPullback f).map e₁.inv ≫ t.hom.app K₁ := by
    rw [← ht, ← Functor.map_comp_assoc, he]
  simpa only [smoothPurityPullbackComparison, t, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc] using hfinal

/-- The canonical comparison tensor constraint, specialized once to finite rings.
Source: blueprint derived tensor comparison (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (((Etale.ordinaryFiniteTensor A X).obj M).obj N) ≅
    ((smoothPurityTensor A X).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj N) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) M).app N

private theorem bifunctorComparison_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : ∀ M N, F.obj ((T.obj M).obj N) ⟶ (S.obj (F.obj M)).obj (F.obj N))
    (hc : ∀ {M M'} (g : M ⟶ M') (N),
      F.map ((T.map g).app N) ≫ c M' N =
        c M N ≫ (S.map (F.map g)).app (F.obj N))
    {M M' : C} (g : M ⟶ M') (N : C) :
    G.map ((T.map g).app N) ≫ e.inv.app ((T.obj M').obj N) ≫ c M' N ≫
        (S.obj (F.obj M')).map (e.hom.app N) ≫
        (S.map (e.hom.app M')).app (G.obj N) =
      e.inv.app ((T.obj M).obj N) ≫ c M N ≫
        (S.obj (F.obj M)).map (e.hom.app N) ≫
        (S.map (e.hom.app M)).app (G.obj N) ≫
        (S.map (G.map g)).app (G.obj N) := by
  rw [e.inv.naturality_assoc, reassoc_of% hc g N]
  rw [← reassoc_of% (S.map (F.map g)).naturality (e.hom.app N)]
  have h := congrArg (fun k ↦ (S.map k).app (G.obj N)) (e.hom.naturality g)
  simp only [Functor.map_comp, NatTrans.comp_app] at h
  rw [h]

private theorem bifunctorComparisonIso_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : ∀ M, T.obj M ⋙ F ≅ F ⋙ S.obj (F.obj M))
    (hc : ∀ {M M'} (g : M ⟶ M') (N),
      F.map ((T.map g).app N) ≫ (c M').hom.app N =
        (c M).hom.app N ≫ (S.map (F.map g)).app (F.obj N))
    {M M' : C} (g : M ⟶ M') (N : C) :
    G.map ((T.map g).app N) ≫
      (Functor.isoWhiskerLeft (T.obj M') e.symm ≪≫ c M' ≪≫
        Functor.isoWhiskerRight e (S.obj (F.obj M')) ≪≫
        Functor.isoWhiskerLeft G (S.mapIso (e.app M'))).hom.app N =
      (Functor.isoWhiskerLeft (T.obj M) e.symm ≪≫ c M ≪≫
        Functor.isoWhiskerRight e (S.obj (F.obj M)) ≪≫
        Functor.isoWhiskerLeft G (S.mapIso (e.app M))).hom.app N ≫
          (S.map (G.map g)).app (G.obj N) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc] using
    bifunctorComparison_naturality T S F G e (fun M N ↦ (c M).hom.app N) hc g N

private theorem comparisonTensor_naturality
    (A : Type uC) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory.map
        (((Etale.derivedTensor A X).map g).app N) ≫
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A M').hom.app N =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A M).hom.app N ≫
        ((ProEtale.derivedTensor A X).map
          ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.map g)).app
            ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj N) := by
  let F := ProEtale.comparisonUpperStar A X
  have hc {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
      (q : L ⟶ L') (V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      F.leftDerivedFunctor.map (((Etale.derivedTensor A X).map q).app V) ≫
        (F.leftDerivedTensorComparison.app L').app V =
      (F.leftDerivedTensorComparison.app L).app V ≫
        ((ProEtale.derivedTensor A X).map (F.leftDerivedFunctor.map q)).app
          (F.leftDerivedFunctor.obj V) := by
    have h := NatTrans.congr_app (F.leftDerivedTensorComparison.naturality q) V
    change F.leftDerivedFunctor.map (((Etale.derivedTensor A X).map q).app V) ≫
      (F.leftDerivedTensorComparison.app L').app V =
      (F.leftDerivedTensorComparison.app L).app V ≫
        ((ProEtale.derivedTensor A X).map (F.leftDerivedFunctor.map q)).app
          (F.leftDerivedFunctor.obj V) at h
    exact h
  have h := bifunctorComparisonIso_naturality
    (Etale.derivedTensor A X) (ProEtale.derivedTensor A X)
    F.leftDerivedFunctor F.mapDerivedCategory F.leftDerivedFunctorIsoMapDerivedCategory
    (fun M ↦ (asIso F.leftDerivedTensorComparison).app M) (fun q V ↦ hc q V) g N
  exact h

/-- Canonical tensor-source comparison in the specified etale presentation.
Source: blueprint tensor mate (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalDualizing f) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (((Etale.ordinaryFiniteTensor P.Coefficient X).obj
            ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₀)).obj
              (P.diagonalOrdinaryDualizing f)) :=
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let M₀ := (Etale.ordinaryFinitePullback P.Coefficient f).obj K₀
  ((smoothPurityTensor P.Coefficient X).mapIso
    (P.smoothPurityPullbackComparison f K K₀ e)).app (P.diagonalDualizing f) ≪≫
    ((smoothPurityTensor P.Coefficient X).obj
      (F.obj M₀)).mapIso (P.diagonalDualizingComparison f) ≪≫
    (smoothPurityComparisonTensor P.Coefficient X M₀
      (P.diagonalOrdinaryDualizing f)).symm

private theorem tensorComparison_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    {K₀ K₁ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (e₀ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e₁ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₁ ≅ K)
    (g : K₀ ⟶ K₁)
    (hg : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g ≫ e₁.hom = e₀.hom) :
    (P.smoothPurityTensorComparison f K K₀ e₀).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            (((Etale.ordinaryFiniteTensor P.Coefficient X).map
              ((Etale.ordinaryFinitePullback P.Coefficient f).map g)).app
                (P.diagonalOrdinaryDualizing f)) =
      (P.smoothPurityTensorComparison f K K₁ e₁).hom := by
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let T := smoothPurityTensor P.Coefficient X
  let h₀ := (P.smoothPurityPullbackComparison f K K₀ e₀).hom
  let h₁ := (P.smoothPurityPullbackComparison f K K₁ e₁).hom
  let a := F.map ((Etale.ordinaryFinitePullback P.Coefficient f).map g)
  have hp : h₀ ≫ a = h₁ := pullbackComparison_naturality P f K e₀ e₁ g hg
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let : (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).PreservesFlat :=
      ProEtale.preservesFlat_comparisonUpperStar
  have hc := comparisonTensor_naturality (ModuleCat.{u + 1} P.Coefficient) X
    ((Etale.ordinaryFinitePullback P.Coefficient f).map g) (P.diagonalOrdinaryDualizing f)
  change F.map (((Etale.ordinaryFiniteTensor P.Coefficient X).map
      ((Etale.ordinaryFinitePullback P.Coefficient f).map g)).app
        (P.diagonalOrdinaryDualizing f)) ≫
      (smoothPurityComparisonTensor P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₁)
        (P.diagonalOrdinaryDualizing f)).hom =
    (smoothPurityComparisonTensor P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₀)
        (P.diagonalOrdinaryDualizing f)).hom ≫
      (T.map a).app (F.obj (P.diagonalOrdinaryDualizing f)) at hc
  have hn := (T.map a).naturality (P.diagonalDualizingComparison f).hom
  dsimp only [smoothPurityTensorComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Category.assoc]
  rw [← cancel_mono (smoothPurityComparisonTensor P.Coefficient X
    ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₁)
    (P.diagonalOrdinaryDualizing f)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [hc]
  simp only [Iso.inv_hom_id_assoc]
  erw [hn]
  simp only [Iso.app_hom, Functor.mapIso_hom]
  change (T.map h₀).app (P.diagonalDualizing f) ≫
      (T.map a).app (P.diagonalDualizing f) ≫
      (T.obj (F.obj ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₁))).map
        (P.diagonalDualizingComparison f).hom =
    (T.map h₁).app (P.diagonalDualizing f) ≫
      (T.obj (F.obj ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₁))).map
        (P.diagonalDualizingComparison f).hom
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, hp]

/-- The canonical tensor mate in the source ordering M tensor omega. The comparison
uses the site pullback square, the monoidal comparison and the actual etale counit
mate. The last arrow is induced by the comparison adjunction unit and the supplied
representative isomorphism, so the target is Rf! K itself.
Source: blueprint def-pur-co-smoothness clause 2 and def-pur-smooth-purity-map
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTheta (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalDualizing f) ⟶
        (P.smoothPurityExceptional f).obj K :=
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  (P.smoothPurityTensorComparison f K K₀ e).hom ≫
    F.map (smoothPurityEtaleTheta P.Coefficient f K₀) ≫
    F.map ((Etale.rightDerivedUpperShriek P.Coefficient f).map
      ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} P.Coefficient) Y).unit.app K₀ ≫
          (ProEtale.comparisonLowerStar
            (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map e.hom)) ≫
    ((P.smoothPurityExceptionalComparison f).app K).inv

private theorem theta_naturality_presentation
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    {K₀ K₁ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (e₀ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e₁ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₁ ≅ K)
    (g : K₀ ⟶ K₁)
    (hg : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g ≫ e₁.hom = e₀.hom) :
    P.smoothPurityTheta f K K₀ e₀ = P.smoothPurityTheta f K K₁ e₁ := by
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  let R := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let H := Etale.rightDerivedUpperShriek P.Coefficient f
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y
  let q₀ := adj.unit.app K₀ ≫ R.map e₀.hom
  let q₁ := adj.unit.app K₁ ≫ R.map e₁.hom
  have hq : g ≫ q₁ = q₀ := by
    dsimp [q₀, q₁]
    rw [← Category.assoc]
    erw [adj.unit.naturality g]
    simp only [Functor.comp_map, Category.assoc]
    change adj.unit.app K₀ ≫ R.map (ν.map g) ≫ R.map e₁.hom = _
    rw [← R.map_comp, hg]
  have ht := smoothPurityEtaleTheta_naturality P.Coefficient f g
  have hc := tensorComparison_naturality P f K e₀ e₁ g hg
  dsimp only [smoothPurityTheta]
  change _ ≫ F.map _ ≫ F.map (H.map q₀) ≫ _ =
    _ ≫ F.map _ ≫ F.map (H.map q₁) ≫ _
  have hm := congrArg F.map ht
  simp only [Functor.map_comp] at hm
  rw [← hq]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hm]
  simp only [← Category.assoc]
  erw [hc]

/-- Canonical second-variable tensor-shift compatibility over an abstract coefficient
category, followed by cancellation of opposite shifts.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShiftGeneric (C : Type uC) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) (M T : _root_.DerivedCategory C) :
    (((curriedTensor (_root_.DerivedCategory C)).obj M).obj (T⟦-r⟧))⟦r⟧ ≅
      ((curriedTensor (_root_.DerivedCategory C)).obj M).obj T :=
  letI := _root_.DerivedCategory.commShiftTensorLeft C M
  (((curriedTensor (_root_.DerivedCategory C)).obj M).commShiftIso r).symm.app _ ≪≫
    ((curriedTensor (_root_.DerivedCategory C)).obj M).mapIso
      ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).app T)

/-- The canonical shift comparison in the published tensor presentation is uniquely
specified by equality, across the two interface types, to the existing K-flat shift.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map).
Proof: rewrite the bifunctor using smoothPurityTensorPresentation. The source and
target then become the source and target of smoothPurityTensorShiftGeneric, so that
isomorphism supplies existence and reflexive heterogeneous equality. If two proposed
isomorphisms satisfy the equation, transitivity of heterogeneous equality gives their
ordinary equality, proving uniqueness. Thus the theorem fixes the isomorphism itself,
including its map, rather than merely asserting that the objects are isomorphic. -/
theorem existsUnique_smoothPurityTensorShift
    (C : Type uC) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :
    ∃! e : ((((ProEtale.derivedTensor C X).obj M).obj (T⟦-r⟧)))⟦r⟧ ≅
      ((ProEtale.derivedTensor C X).obj M).obj T,
      HEq e (smoothPurityTensorShiftGeneric (Sheaf (Scheme.ProEt.topology X) C) r M T) := by
  exact ⟨_, HEq.rfl, fun e h ↦ eq_of_heq h⟩

/-- The published canonical shift comparison, selected by its exact map identity.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShiftCoefficients (C : Type uC) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :
    ((((ProEtale.derivedTensor C X).obj M).obj (T⟦-r⟧)))⟦r⟧ ≅
      ((ProEtale.derivedTensor C X).obj M).obj T :=
  (existsUnique_smoothPurityTensorShift C X r M T).exists.choose

/-- Specialization of canonical tensor-shift compatibility to finite module coefficients.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorShift (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (r : ℤ)
    (M T : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (((smoothPurityTensor A X).obj M).obj (T⟦-r⟧))⟦r⟧ ≅
      ((smoothPurityTensor A X).obj M).obj T :=
  smoothPurityTensorShiftCoefficients (ModuleCat.{u + 1} A) X r M T

/-- Canonical twist reassociation. T is the already shifted coefficient line A(d)[2d];
T[-2d] is its canonical inverse-shift presentation A(d). The first factor is tensor's
shift compatibility in the second variable; the second cancels the opposite shifts.
On total K-flat tensor complexes these are exactly the usual shift identifications.
Source: blueprint def-pur-smooth-purity-map, tau
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityReassociation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    (((smoothPurityTensor P.Coefficient X).obj M).obj
      ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧ ≅
      ((smoothPurityTensor P.Coefficient X).obj M).obj
        (P.diagonalTwist X d) :=
  smoothPurityTensorShift P.Coefficient X (2 * (d : ℤ)) M (P.diagonalTwist X d)

/-- The recorded exceptional functor with its source-implied compactification supplied.
Source: blueprint finite purity domain (blueprint: def-pur-smooth-purity-map). -/
def smoothPurityExceptionalOver (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) ⥤
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  P.smoothPurityExceptional f

/-- The tensor form gamma^sm = (1 tensor Pi^-1) followed by the specified theta.
Pi is precisely the normalized diagonal orientation, never an arbitrary endpoint iso.
The finite-type field domain supplies compactification internally.
Source: blueprint main-20261015 def-pur-smooth-purity-map, displayed tensor composite
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorMapInPresentation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj (P.diagonalTwist X d) ⟶
        (P.smoothPurityExceptionalOver f aY).obj K :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  ((smoothPurityTensor P.Coefficient X).obj
    ((P.smoothPurityPullback f).obj K)).map
      (P.diagonalDualizingObject d f aY).inv ≫
    P.smoothPurityTheta f K K₀ e

/-- The tensor-composite source on the original intrinsic coefficient object.
The inverse of the canonical realization equivalence only changes its presentation.
Source: blueprint def-pur-smooth-purity-map, tensor source
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  ((smoothPurityTensor P.Coefficient X).obj
    ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).obj
        (P.diagonalTwist X d)

/-- The uniquely determined tensor composite, characterized in every etale
presentation of the original intrinsic coefficient object. This is the displayed
formula 1 tensor Pi^-1 followed by theta, rather than a bare existence of an iso.
Source: blueprint main-20261015 def-pur-smooth-purity-map
(blueprint: def-pur-smooth-purity-map).

Proof: finite constructible origin supplies a bounded etale representative of K.
The comparison unit is invertible on bounded-below etale objects; the triangle
identities give an invertible counit on K. Thus Rnu_* K is a canonical representative.
Use its counit inverse in the pullback/tensor comparison, then tensor with the fixed
inverse diagonal orientation and apply the counit mate theta. For any other
representative e, naturality of the comparison unit and its triangle identities
identify the last two factors of smoothPurityTheta with the exceptional comparison.
The monoidal comparison is natural in both variables, and the pullback square is
natural in K. Hence conjugating by e gives exactly smoothPurityTensorMapInPresentation.
This proves existence with the stated equality for every representative. Since at
least one representative exists, that equality determines the morphism uniquely.
No representative, root, basis, orientation or endpoint iso is chosen as map data. -/
theorem existsUnique_smoothPurityTensorMap (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (_hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃! g : P.smoothPurityTensorSource f d K ⟶
      (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
      ∀ (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
        (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅
            (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
        g = P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e := by
  classical
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  have hc := (Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K
  have hOrigin : (ObjectProperty.ι
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).essImage K := by
    apply hc.mpr
    refine ⟨_hK.1.2, ?_⟩
    obtain ⟨a, ha⟩ := _hK.1.1.bddBelow
    obtain ⟨b, hb⟩ := _hK.1.1.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hn))) hi
    · exact (not_lt_of_ge ((hb hn).trans (le_max_right a b))) hi
  obtain ⟨J, ⟨eJ⟩⟩ := hOrigin
  let : (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).Additive
  let ecomp := (Functor.mapDerivedCategoryCompIso ν
    (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor).app J.obj
  let e : ν.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
    E.functor.preimageIso (ecomp.symm ≪≫ eJ ≪≫ (E.counitIso.app K).symm)
  have hplus : _root_.DerivedCategory.TStructure.t.plus J.obj := by
    obtain ⟨a, b, _, hz⟩ := J.property.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff J.obj a).mpr
      (fun i hi ↦ hz i (.inl hi))⟩
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let : HasCompactification f := inferInstance
  let gcan := P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
    (E.inverse.obj K) J.obj e
  have hcan (K₀ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e₀ : ν.mapDerivedCategory.obj K₀ ≅ E.inverse.obj K) :
      gcan = P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
        (E.inverse.obj K) K₀ e₀ := by
    obtain ⟨q, hq⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      K₀ J.obj hplus).surjective (e₀.hom ≫ e.inv)
    change ν.mapDerivedCategory.map q = e₀.hom ≫ e.inv at hq
    have hqe : ν.mapDerivedCategory.map q ≫ e.hom = e₀.hom := by
      rw [hq]
      simp
    have ht := theta_naturality_presentation P f (E.inverse.obj K) e₀ e q hqe
    dsimp only [gcan, smoothPurityTensorMapInPresentation]
    rw [ht]
  exact ⟨gcan, hcan, fun g hg ↦ (hg J.obj e).trans (hcan J.obj e).symm⟩

/-- The canonical tensor form gamma^sm on the actual intrinsic pro-etale object K.
The theorem specifies a unique morphism by the explicit composite in every
presentation, so its use postpones only a proof and never unspecified map data.
Source: blueprint def-pur-smooth-purity-map, gamma^sm
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityTensorMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose

/-- The smooth purity map gamma = gamma^sm after tau, in the original intrinsic
small-pro-etale derived category. Its source is Lf* K(d)[2d] using the canonical
inverse-shift presentation of the recorded shifted Tate line. Its target is the
canonical realization of the recorded exceptional inverse image of K.
Source: blueprint def-pur-smooth-purity-map, final composite
(blueprint: def-pur-smooth-purity-map). -/
def smoothPurityMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).hom ≫
    P.smoothPurityTensorMap f d K hK

end WeilConjectures.PurityFiniteSetting
