/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-! # Naturality of the projection-and-counit tensor transpose

Source: blueprint main-20261015, smooth purity,
prop-pur-smooth-purity-naturality-cover.proof.md, first sentence
(blueprint: lem-pur-tensor-map-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u uC
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

private theorem tensorMap_etaleTheta_naturality
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

private theorem tensorMap_smoothPurityEtaleTheta_naturality
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
  erw [reassoc_of% hs, tensorMap_etaleTheta_naturality]

private theorem tensorMap_bifunctorComparison_naturality
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

private theorem tensorMap_bifunctorComparisonIso_naturality
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
    tensorMap_bifunctorComparison_naturality T S F G e (fun M N ↦ (c M).hom.app N) hc g N

private theorem tensorMap_comparisonTensor_naturality
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
  have h := tensorMap_bifunctorComparisonIso_naturality
    (Etale.derivedTensor A X) (ProEtale.derivedTensor A X)
    F.leftDerivedFunctor F.mapDerivedCategory F.leftDerivedFunctorIsoMapDerivedCategory
    (fun M ↦ (asIso F.leftDerivedTensorComparison).app M) (fun q V ↦ hc q V) g N
  exact h

private theorem tensorMap_pullbackComparison_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    {K₀ K₁ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (e₀ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e₁ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₁ ≅ K')
    (u : K ⟶ K')
    (g : K₀ ⟶ K₁)
    (hg : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g ≫ e₁.hom = e₀.hom ≫ u) :
    (P.smoothPurityPullbackComparison f K K₀ e₀).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            ((Etale.ordinaryFinitePullback P.Coefficient f).map g) =
      (P.smoothPurityPullback f).map u ≫
        (P.smoothPurityPullbackComparison f K' K₁ e₁).hom := by
  have he : e₀.inv ≫ (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g = u ≫ e₁.inv := by
    rw [← cancel_mono e₁.hom]
    simp [Category.assoc, hg]
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
      (P.smoothPurityPullback f).map u ≫
        (P.smoothPurityPullback f).map e₁.inv ≫ t.hom.app K₁ := by
    rw [← ht, ← Functor.map_comp_assoc, he, Functor.map_comp, Category.assoc]
  simpa only [smoothPurityPullbackComparison, t, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc] using hfinal

private theorem tensorMap_tensorComparison_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    {K₀ K₁ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (e₀ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e₁ : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₁ ≅ K')
    (u : K ⟶ K')
    (g : K₀ ⟶ K₁)
    (hg : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map g ≫ e₁.hom = e₀.hom ≫ u) :
    (P.smoothPurityTensorComparison f K K₀ e₀).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            (((Etale.ordinaryFiniteTensor P.Coefficient X).map
              ((Etale.ordinaryFinitePullback P.Coefficient f).map g)).app
                (P.diagonalOrdinaryDualizing f)) =
      ((smoothPurityTensor P.Coefficient X).map
        ((P.smoothPurityPullback f).map u)).app (P.diagonalDualizing f) ≫
        (P.smoothPurityTensorComparison f K' K₁ e₁).hom := by
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let T := smoothPurityTensor P.Coefficient X
  let h₀ := (P.smoothPurityPullbackComparison f K K₀ e₀).hom
  let h₁ := (P.smoothPurityPullbackComparison f K' K₁ e₁).hom
  let a := F.map ((Etale.ordinaryFinitePullback P.Coefficient f).map g)
  let b := (P.smoothPurityPullback f).map u
  have hp : h₀ ≫ a = b ≫ h₁ :=
    tensorMap_pullbackComparison_naturality P f K K' e₀ e₁ u g hg
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let : (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).PreservesFlat :=
      ProEtale.preservesFlat_comparisonUpperStar
  have hc := tensorMap_comparisonTensor_naturality (ModuleCat.{u + 1} P.Coefficient) X
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
    (T.map b).app (P.diagonalDualizing f) ≫
      (T.map h₁).app (P.diagonalDualizing f) ≫
      (T.obj (F.obj ((Etale.ordinaryFinitePullback P.Coefficient f).obj K₁))).map
        (P.diagonalDualizingComparison f).hom
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, hp, T.map_comp,
    NatTrans.comp_app, Category.assoc]

/-- The displayed inverse-projection/counit input in ordinary etale coordinates.
This is the inverse adjunction image of the already specified tensor mate, including
its source symmetry and the canonical identification of the degree-zero unit. Expanding
smoothPurityEtaleTheta and projectionTensorMap gives exactly F(symmetry), PF inverse,
counit tensor identity and the left unitor. No arrow is chosen from an existence result.
Source: main-20261015, def-pur-co-smoothness clause 2 and the displayed a_K in
lem-pur-tensor-map-naturality (blueprint: lem-pur-tensor-map-naturality). -/
noncomputable def purityTensorCoefficientInput
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      (((Etale.ordinaryFiniteTensor A X).obj
        ((Etale.ordinaryFinitePullback A f).obj K₀)).obj
          ((Etale.rightDerivedUpperShriek A f).obj
            (Etale.ordinaryFiniteUnit A Y))) ⟶ K₀ :=
  ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ K₀).symm
    (smoothPurityEtaleTheta A f K₀)

/-- The coefficient square after the canonical site comparison. The normalized compact-
support comparison identifies this with u composed with a_K equals a_K' composed with
F(m tensor identity). This is an equality of pro-etale derived morphisms, expressed in
etale-origin coordinates exactly as in the recorded cohomological-smoothness definition.
Source: main-20261015, lem-pur-tensor-map-naturality, second displayed equation
(blueprint: lem-pur-tensor-map-naturality). -/
def PurityTensorCoefficientSquare
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) (u₀ : K₀ ⟶ K₀') : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      (purityTensorCoefficientInput A f K₀ ≫ u₀) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((Etale.ordinaryFiniteTensor A X).map
          ((Etale.ordinaryFinitePullback A f).map u₀)).app
            ((Etale.rightDerivedUpperShriek A f).obj
              (Etale.ordinaryFiniteUnit A Y))) ≫ purityTensorCoefficientInput A f K₀')

/-- Naturality of the specified tensor mate and its equivalent coefficient square.
K and K' are arbitrary original pro-etale Dctf objects. Their etale representatives,
representing isomorphisms and a compatible lifted arrow are coordinates, not restrictions:
finite constructible complexes have etale origins and comparison is fully faithful there.
The equation is asserted for every such presentation. The compactification is supplied
by the finite-type geometry; no compactification hypothesis is added.
Source: main-20261015, prop-pur-smooth-purity-naturality-cover.proof.md, first sentence
(blueprint: lem-pur-tensor-map-naturality).
Proof:
1. Naturality of the etale tensor mate: apply projectionTensorMap_naturality_right to the
compact-support adjunction and the natural projection map, then the naturality of the left
unitor; tensor interchange at the degree-zero unit comparison and naturality of the tensor
symmetry give naturality of smoothPurityEtaleTheta in K0.
2. The comparison tensor constraint and the pullback comparison are natural in the first
variable (naturality of leftDerivedTensorComparison, of sfDerivedComparisonPullbackIso, and the
compatibility of u0 with u through e, e'), so the tensor-source comparison square commutes.
3. With q = unit followed by the derived lower star of e.hom, naturality of the comparison
unit gives q0 followed by R(u) equals u0 followed by q1. Pasting this with steps 1 and 2 and
the naturality of smoothPurityExceptionalComparison.inv gives the theta square.
4. The inverse-transpose of the step 1 square (homEquiv naturality of the compact-support
adjunction), mapped by the comparison pullback, is PurityTensorCoefficientSquare.
No orientation or smooth purity isomorphism is used. -/
theorem purityTensorMap_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y K)
    (_hK' : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y K')
    (u : K ⟶ K')
    (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e' : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀' ≅ K')
    (u₀ : K₀ ⟶ K₀')
    (_hu : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map u₀ ≫ e'.hom = e.hom ≫ u) :
    @smoothPurityTheta P X Y f
        (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
        K K₀ e ≫
      (@smoothPurityExceptional P X Y f
        (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification).map
        u =
      ((smoothPurityTensor P.Coefficient X).map
        ((P.smoothPurityPullback f).map u)).app
          (@diagonalDualizing P X Y f
            (P.finiteComparedCompactification f
              (Y ↘ Spec (.of P.field.k))).hasCompactification) ≫
        @smoothPurityTheta P X Y f
          (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
          K' K₀' e' ∧
    @PurityTensorCoefficientSquare P.Coefficient _ _ X Y f
      (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
      K₀ K₀' u₀ := by
  let := (P.finiteComparedCompactification f
    (Y ↘ Spec (.of P.field.k))).hasCompactification
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  let R := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let H := Etale.rightDerivedUpperShriek P.Coefficient f
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y
  let q₀ := adj.unit.app K₀ ≫ R.map e.hom
  let q₁ := adj.unit.app K₀' ≫ R.map e'.hom
  have hq : q₀ ≫ R.map u = u₀ ≫ q₁ := by
    symm
    dsimp [q₀, q₁]
    rw [← Category.assoc]
    erw [adj.unit.naturality u₀]
    simp only [Functor.comp_map, Category.assoc]
    change adj.unit.app K₀ ≫ R.map (ν.map u₀) ≫ R.map e'.hom =
      adj.unit.app K₀ ≫ R.map e.hom ≫ R.map u
    rw [← R.map_comp, _hu, R.map_comp]
  have ht := tensorMap_smoothPurityEtaleTheta_naturality P.Coefficient f u₀
  have hc := tensorMap_tensorComparison_naturality P f K K' e e' u u₀ _hu
  constructor
  · have hfinal : (P.smoothPurityTensorComparison f K K₀ e).hom ≫
          F.map (smoothPurityEtaleTheta P.Coefficient f K₀) ≫
          F.map (H.map q₀) ≫ F.map (H.map (R.map u)) =
        ((smoothPurityTensor P.Coefficient X).map
          ((P.smoothPurityPullback f).map u)).app (P.diagonalDualizing f) ≫
          (P.smoothPurityTensorComparison f K' K₀' e').hom ≫
          F.map (smoothPurityEtaleTheta P.Coefficient f K₀') ≫ F.map (H.map q₁) := by
      rw [← F.map_comp, ← H.map_comp, hq]
      have hm := congrArg F.map ht
      simp only [Functor.map_comp] at hm
      simp only [Functor.map_comp]
      erw [← reassoc_of% hm]
      simp only [← Category.assoc]
      erw [hc]
    have he := (P.smoothPurityExceptionalComparison f).inv.naturality u
    dsimp only [Functor.comp_map] at he
    dsimp only [smoothPurityTheta]
    simp only [Iso.app_inv, Category.assoc]
    erw [← he]
    simpa only [Category.assoc, Iso.app_inv] using congrArg
      (fun z ↦ z ≫ ((P.smoothPurityExceptionalComparison f).app K').inv) hfinal
  · apply congrArg ν.map
    let adjf := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
    exact (adjf.homEquiv_naturality_right_square _ _ _ _ ht).symm

end WeilConjectures.PurityFiniteSetting
