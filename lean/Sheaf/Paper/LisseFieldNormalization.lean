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
(blueprint: def-real-lisse-field-normalization).
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
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- Finite scalar comparison normalized through the recorded completion map chi and
ordinary multiplication of scalar factors. Source: BS 6.8.2, 6.8.15
(blueprint: def-real-lisse-field-normalization). -/
structure FieldNormalized (i : E →ₐ[ℚ_[l]] F) (X : Base D l hl)
    (aE : At D l hl E X) (aF : At D l hl F X)
    (b : FieldChange D l hl E F i X aE aF) where
  square : WeilConjectures.completedCoefficientMap l E F i X.scheme ≫ scalar D l hl F aF =
    scalar D l hl E aE ≫ b.coefficient
  ordinary : completedOrdinaryScalarExtension l E F i X.scheme ≅
    pbcExtend (WeilConjectures.completedCoefficientMap l E F i X.scheme)
  sections : ∀ (M : integralTowerModules l E X.scheme) (U : X.scheme.ProEtᵒᵖ)
    (c : (completedIntegralCommRingSheafUnrestricted l F X.scheme).obj.obj U)
    (m : M.val.obj U),
    (ordinary.hom.app M).val.app U (completedScalarTensorSection l E F i X.scheme M U c m) =
      pbcTensorSection (WeilConjectures.completedCoefficientMap l E F i X.scheme) M U c m
  ambient : completedDerivedScalarExtension l E F i X.scheme ≅
    pbcDerivedExtend (WeilConjectures.completedCoefficientMap l E F i X.scheme)
  ambient_normalized : ∀ P : CochainComplex (integralTowerModules l E X.scheme) ℤ,
    (completedScalarCounit l E F i X.scheme P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        pbcComplexCounit (WeilConjectures.completedCoefficientMap l E F i X.scheme) P
  chi : ∀ K : sfIntegralConstructibleCategory l E X.scheme,
    ((completedDerivedScalarExtension l E F i X.scheme).obj K.obj ≅
      (integralScalarExtensionOfUniverses l E F i X.scheme).obj K.obj)
  chi_normalized : ∀ K : sfIntegralConstructibleCategory l E X.scheme,
    (chi K).hom = (completedScalarComparison l E F i X.scheme).app K.obj
  derived : sfRationalScalarExtension l E X.scheme D.p hl F i ⋙ aF.J ≅
    aE.J ⋙ pbcDerivedExtend b.coefficient
  derived_normalized : ∀ K : sfIntegralConstructibleCategory l E X.scheme,
    HEq (derived.hom.app ((sfRationalConstructibleLocalization l E X.scheme).obj K))
      (aF.integral.hom.app
          ((sfConstructibleIntegralScalarExtension D.p l hl E F i X.scheme).obj K) ≫
        (pbcDerivedExtend (scalar D l hl F aF)).map (chi K).inv ≫
        (pbcDerivedExtend (scalar D l hl F aF)).map (ambient.hom.app K.obj) ≫
        (pbcReductionNormalization
          (WeilConjectures.completedCoefficientMap l E F i X.scheme) (scalar D l hl F aF)
          (scalar D l hl E aE ≫ b.coefficient) square K.obj).hom ≫
        (pbcReductionNormalization (scalar D l hl E aE) b.coefficient
          (scalar D l hl E aE ≫ b.coefficient) rfl K.obj).inv ≫
        (pbcDerivedExtend b.coefficient).map (aE.integral.inv.app K))
  [additive : (pbcExtend b.coefficient).Additive]
  [limits : PreservesFiniteLimits (pbcExtend b.coefficient)]
  [colimits : PreservesFiniteColimits (pbcExtend b.coefficient)]
  exact : pbcDerivedExtend b.coefficient ≅ (pbcExtend b.coefficient).mapDerivedCategory
  exact_normalized : ∀ P : CochainComplex (Modules D l hl E X) ℤ,
    exact.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcExtend b.coefficient).mapDerivedCategoryFactors.hom.app P =
      pbcComplexCounit b.coefficient P
  heart : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    ∃ e : aE.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj ((aE.sheaf D l hl E).obj K),
      ((DerivedCategory.homologyFunctor _ 0).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ = 𝟙 _) ∧
      (DerivedCategory.homologyFunctor _ 0).map
        (derived.hom.app K ≫ (pbcDerivedExtend b.coefficient).map e.hom ≫
          exact.hom.app _ ≫ (Functor.mapDerivedCategorySingleFunctor
            (pbcExtend b.coefficient) 0).hom.app _) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
      (b.comparison K hK).hom


end WeilConjectures.LisseRealization
