/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.LisseRationalRealizationData
public import Sheaf.Paper.LisseTensorNormalization
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback

/-! # Canonically normalized lisse realization

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: def-real-lisse-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- The integral-to-rational pullback square, fixed on the actual adjunction units.
The derived comparison is computed by precisely the ordinary completion map of the
recorded dependency. Source: BS 6.8.15 (blueprint: def-real-lisse-pullback-normalization). -/
structure PullNormalized {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) (af : Along D l hl E f aX aY) where
  [ordinaryAdditive : (ordinaryPull l E f).Additive]
  ordinary : ordinaryIntegralModulePull l E f ⋙ pbcExtend (scalar D l hl E aX) ≅
    pbcExtend (scalar D l hl E aY) ⋙ ordinaryPull l E f
  sections : ∀ (M : integralTowerModules l E Y.scheme) (U : Y.scheme.ProEt)
    (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (pbcTensorSection (scalar D l hl E aX) ((ordinaryIntegralModulePull l E f).obj M)
        (op ((proEtaleBaseChange f).obj U)) 1
        (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op U) m)) =
    ContinuousRational.moduleUnit f (coefficientPull l E f)
      ((pbcExtend (scalar D l hl E aY)).obj M) U
      (pbcTensorSection (scalar D l hl E aY) M (op U) 1 m)
  derived : ordinaryIntegralDerivedPull l E f ⋙ pbcDerivedExtend (scalar D l hl E aX) ≅
    pbcDerivedExtend (scalar D l hl E aY) ⋙
      ContinuousRational.derivedPull f (coefficientPull l E f)
  counit : DerivedCategory.Q ⋙ ContinuousRational.derivedPull f (coefficientPull l E f) ⟶
    (ordinaryPull l E f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  counit_normalized : ContinuousRational.IsNormalizedPullCounit f
    (coefficientPull l E f) counit
  derived_normalized : ∀ P : CochainComplex (integralTowerModules l E Y.scheme) ℤ,
    (pbcDerivedExtend (scalar D l hl E aX)).map (ordinaryIntegralPullComplexCounit l E f P) ≫
        pbcComplexCounit (scalar D l hl E aX) ((ordinaryIntegralPullComplex l E f).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
      derived.hom.app (DerivedCategory.Q.obj P) ≫
        (ContinuousRational.derivedPull f (coefficientPull l E f)).map
          (pbcComplexCounit (scalar D l hl E aY) P) ≫
        counit.app (rationalComplex D l hl E aY P)
  degree_zero : ∀ (M : Modules D l hl E Y), M.IsFiniteLocallyFree →
    ((ContinuousRational.derivedPull f (coefficientPull l E f)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
    (DerivedCategory.singleFunctor _ 0).obj ((ordinaryPull l E f).obj M))
  degree_zero_normalized : ∀ (M : Modules D l hl E Y) (hM : M.IsFiniteLocallyFree),
    (degree_zero M hM).hom =
      (ContinuousRational.derivedPull f (coefficientPull l E f)).map
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app M) ≫
      counit.app ((CochainComplex.singleFunctor _ 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ordinaryPull l E f) (.up ℤ) 0).hom.app M) ≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app ((ordinaryPull l E f).obj M)
  comparison : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    aX.J.obj ((pull D l hl E f).obj
      ((sfRationalConstructibleLocalization l E Y.scheme).obj K)) ≅
    (ContinuousRational.derivedPull f (coefficientPull l E f)).obj (aY.J.obj
      ((sfRationalConstructibleLocalization l E Y.scheme).obj K))
  integralCompletion : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    (ordinaryIntegralDerivedPull l E f).obj K.obj ≅ (integralDerivedPullback l E f).obj K.obj
  integralCompletion_normalized : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    (integralCompletion K).hom = (ordinaryIntegralCompletionComparison l E f).app K.obj
  normalized : ∀ K : sfIntegralConstructibleCategory l E Y.scheme,
    HEq (comparison K).hom
      (aX.integral.hom.app ((constructibleIntegralPullback l E f).obj K) ≫
        (pbcDerivedExtend (scalar D l hl E aX)).map
          (integralCompletion K).inv ≫
        derived.hom.app K.obj ≫
        (ContinuousRational.derivedPull f (coefficientPull l E f)).map
          (aY.integral.inv.app K))
  heart : ∀ (K : sfIntegralConstructibleCategory l E Y.scheme)
    (hK : Lisse D l hl E Y ((sfRationalConstructibleLocalization l E Y.scheme).obj K)),
    ∃ e : aY.J.obj ((sfRationalConstructibleLocalization l E Y.scheme).obj K) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((aY.sheaf D l hl E).obj ((sfRationalConstructibleLocalization l E Y.scheme).obj K)),
      ((DerivedCategory.homologyFunctor _ 0).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ = 𝟙 _) ∧
      (DerivedCategory.homologyFunctor _ 0).map
        ((comparison K).hom ≫
          (ContinuousRational.derivedPull f (coefficientPull l E f)).map e.hom ≫
          (degree_zero _ ((aY.image _).mpr
            ⟨_, hK, ⟨Iso.refl _⟩⟩)).hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
      (af.comparison _ hK).hom


end WeilConjectures.LisseRealization
