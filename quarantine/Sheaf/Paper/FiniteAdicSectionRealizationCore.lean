/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.AdicSectionCanonicalModels

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-section-realization-core).

This module records one component of the canonical finite section diagrams.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace AdicCompactificationSections

open scoped ChangeOfRings

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The base point carries its identity structure morphism.
Source: the finite-field convention
(blueprint: def-a1-finite-adic-section-realization-core). -/
instance pointOver : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩

/-- Reuse the family's existing additive structure at its literal module-pullback
presentation, so the single-complex comparison can infer zero preservation.
Source: BS 6.8.15 (blueprint: def-a1-finite-adic-section-realization-core). -/
instance familyModulePullAdditive (R : ContinuousRational.Family.{u} l)
    {X Y : ContinuousRational.Base.{u} l} (f : X.scheme ⟶ Y.scheme) :
    (ContinuousRational.modulePull f (R.along E (X := X) (Y := Y) f).coefficient).Additive :=
  (R.along E (X := X) (Y := Y) f).ordinaryAdditive

/-- The canonical single-complex comparison, using the given pullback additivity.
Source: BS 6.8.15 (blueprint: def-a1-finite-adic-section-realization-core). -/
def familyPullSingle (R : ContinuousRational.Family.{u} l)
    {X Y : ContinuousRational.Base.{u} l} (f : X.scheme ⟶ Y.scheme) :
    CochainComplex.singleFunctor _ 0 ⋙
        (ContinuousRational.modulePull f
          (R.along E (X := X) (Y := Y) f).coefficient).mapHomologicalComplex (.up ℤ) ≅
      ContinuousRational.modulePull f (R.along E (X := X) (Y := Y) f).coefficient ⋙
        CochainComplex.singleFunctor _ 0 :=
  letI := (R.along E (X := X) (Y := Y) f).ordinaryAdditive
  HomologicalComplex.singleMapHomologicalComplex _ (.up ℤ) 0

/-- The direct-image compositor is the mate of the specified derived pullback
compositor, with respect to the actual continuous derived adjunctions.
Source: BS 6.8.15; Milne 18.3(b)
(blueprint: def-a1-finite-adic-section-realization-core). -/
def derivedPushCompositor (R : ContinuousRational.Family.{u} l)
    (o : ∀ {X Y : ContinuousRational.Base.{u} l} (f : X.scheme ⟶ Y.scheme),
      ContinuousRational.DirectImage.Ordinary l E f
        (R.realization E X) (R.realization E Y) (R.along E f))
    {X Y Z : ContinuousRational.Base.{u} l}
    (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme) :
    ContinuousRational.DirectImage.derivedPush h (R.along E h).coefficient ⋙
        ContinuousRational.DirectImage.derivedPush g (R.along E g).coefficient ≅
      ContinuousRational.DirectImage.derivedPush (h ≫ g)
        (R.along E (h ≫ g)).coefficient :=
  conjugateIsoEquiv ((o g).adjunction.comp (o h).adjunction)
    (o (h ≫ g)).adjunction (R.composition E g h).ambient

/-- Apply proper direct image to the adjunct of the specified open inverse unit,
then the actual direct-image compositor. This construction has no reference to
any proposed H⁰/Hom identification or restriction formula.
Source: Milne 18.1, 18.3(b); BS 6.8.15
(blueprint: def-a1-finite-adic-section-realization-core). -/
def derivedCompactOrdinaryArrow (R : ContinuousRational.Family.{u} l)
    (o : ∀ {X Y : ContinuousRational.Base.{u} l} (f : X.scheme ⟶ Y.scheme),
      ContinuousRational.DirectImage.Ordinary l E f
        (R.realization E X) (R.realization E Y) (R.along E f))
    {X Y Z : ContinuousRational.Base.{u} l}
    (b : X.scheme ⟶ Y.scheme) (j : Z.scheme ⟶ X.scheme)
    (K : DerivedCategory (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)))
    (M : DerivedCategory (pbcModules Z.scheme (rationalCoefficientSheaf l Z.scheme E)))
    (t : (ContinuousRational.derivedPull j (R.along E j).coefficient).obj K ⟶ M) :
    (ContinuousRational.DirectImage.derivedPush b (R.along E b).coefficient).obj K ⟶
      (ContinuousRational.DirectImage.derivedPush (j ≫ b)
        (R.along E (j ≫ b)).coefficient).obj M :=
  (ContinuousRational.DirectImage.derivedPush b (R.along E b).coefficient).map
      ((o (X := Z) (Y := X) j).adjunction.homEquiv K M t) ≫
    (derivedPushCompositor l E R o b j).hom.app M

set_option maxHeartbeats 800000 in
-- Elaborating the normalization diagrams unfolds several derived coefficient transports.
/-- The finite-field part of the section realization. Its realization is fixed on
integral representatives by continuous tensor, including every rational fraction.
The cohomology functor has exactly the already recorded H⁰ objects. The natural
comparison is normalized by evaluation at 1 after the ordinary module-unit Hom map.
Source: BS 6.8.14(2); Milne 18.1
(blueprint: def-a1-finite-adic-section-realization-core). -/
structure FiniteAtCore (R : ContinuousRational.Family.{u} l) (W : Geometry D) where
  J : sfRationalConstructibleCategory l E W.scheme ⥤
    DerivedCategory (pbcModules W.scheme (rationalCoefficientSheaf l W.scheme E))
  integral : sfRationalConstructibleLocalization l E W.scheme ⋙ J ≅
    (sfIntegralConstructible l E W.scheme).ι ⋙ integralDetailedTransport W.scheme l E ⋙
      pbcDerivedExtend
        ((R.realization E (realizationBase D l hl W)).integralIso.hom ≫
          (R.realization E (realizationBase D l hl W)).inclusion)
  [J_additive : J.Additive]
  [J_linear : J.Linear E]
  faithfully : ∀ K M, Function.Bijective (J.map : (K ⟶ M) → (J.obj K ⟶ J.obj M))
  sheaf : sfRationalHeart l E W.scheme ⥤
    pbcModules W.scheme (rationalCoefficientSheaf l W.scheme E)
  heart : (sfRationalHeartProperty l E W.scheme).ι ⋙ J ≅
    sheaf ⋙ DerivedCategory.singleFunctor _ 0
  unit : sfRationalHeart l E W.scheme
  unit_obj : unit.obj = rationalCohomologyCoefficient D l hl E W.scheme
  unit_sheaf : sheaf.obj unit ≅
    SheafOfModules.unit (proEtaleModuleCoefficients (rationalCoefficientSheaf l W.scheme E))
  unit_model : CoefficientUnitModel l E W.scheme
    ((R.realization E (realizationBase D l hl W)).integralIso.hom ≫
      (R.realization E (realizationBase D l hl W)).inclusion)
  unit_realization : heart.hom.app unit ≫
      (DerivedCategory.singleFunctor _ 0).map unit_sheaf.hom =
    J.map (eqToHom unit_obj) ≫
      integral.hom.app (integralCohomologyCoefficient D l hl E W.scheme) ≫
      coefficientUnitArrow D l hl E W.scheme
        ((R.realization E (realizationBase D l hl W)).integralIso.hom ≫
          (R.realization E (realizationBase D l hl W)).inclusion) unit_model
  ordinary : sfRationalHeart l E W.scheme ⥤ ModuleCat.{u} E
  ordinary_obj : ∀ F, ordinary.obj F =
    rationalOrdinaryCohomology D l hl E W.scheme F.obj 0
  /-- The direct-image comparison supplies the actual derived adjunction and its
  coefficient normalization for the structure map to `Spec k`. -/
  direct_image : ∀ {X Y : ContinuousRational.Base l} (f : X.scheme ⟶ Y.scheme),
    AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.Ordinary l E f
      (R.realization E X) (R.realization E Y) (R.along E f)
  point : PointSection D l hl E R
  image : ∀ F : sfRationalConstructibleCategory l E W.scheme,
    point.J.obj (rationalImage D l hl E W.scheme F) ≅
      (ContinuousRational.DirectImage.derivedPush (W.scheme ↘ Spec (.of D.k))
        (R.along E (X := realizationBase D l hl W)
          (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
            (W.scheme ↘ Spec (.of D.k))).coefficient).obj (J.obj F)
  image_model : ∀ F : sfRationalConstructibleCategory l E W.scheme,
    ImageModel D l hl E W F.obj


end AdicCompactificationSections
end WeilConjectures
