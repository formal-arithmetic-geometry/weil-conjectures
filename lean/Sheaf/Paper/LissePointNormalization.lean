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
(blueprint: def-real-lisse-point-normalization).
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
/-- The point comparison is the actual sections/localization map on integral models.
The ordinary map sends c tensor m to c times the image of m; the derived map is its
termwise localization. Source: BS 6.8.2, 6.8.14(2)
(blueprint: def-real-lisse-point-normalization). -/
structure PointNormalized (a : At D l hl E (point D l hl)) (p : PointAt D l hl E a) where
  [additive : (sections D l hl E).Additive]
  [limits : PreservesFiniteLimits (sections D l hl E)]
  [colimits : PreservesFiniteColimits (sections D l hl E)]
  [scalarLimits : PreservesFiniteLimits (pbcExtend (scalar D l hl E a))]
  [scalarColimits : PreservesFiniteColimits (pbcExtend (scalar D l hl E a))]
  [compositionLimits : PreservesFiniteLimits
    (pbcExtend (scalar D l hl E a) ⋙ sections D l hl E)]
  [compositionColimits : PreservesFiniteColimits
    (pbcExtend (scalar D l hl E a) ⋙ sections D l hl E)]
  ordinary : pointCompletedSections D.k l E ⋙ pointModuleRationalization l E ≅
    pbcExtend (scalar D l hl E a) ⋙ sections D l hl E
  sections : ∀ (M : integralTowerModules l E (point D l hl).scheme)
    (c : E) (m : (pointCompletedSections D.k l E).obj M),
    (ordinary.hom.app M) (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] m) =
      pbcTensorSection (scalar D l hl E a) M (op (ProEt.mk (𝟙 _)))
        (pointConstants D l E c) m
  exact : pbcDerivedExtend (scalar D l hl E a) ≅
    (pbcExtend (scalar D l hl E a)).mapDerivedCategory
  exact_normalized : ∀ P : CochainComplex (integralTowerModules l E (point D l hl).scheme) ℤ,
    exact.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcExtend (scalar D l hl E a)).mapDerivedCategoryFactors.hom.app P =
      pbcComplexCounit (scalar D l hl E a) P
  derived : pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E ≅
    pbcDerivedExtend (scalar D l hl E a) ⋙ (LisseRealization.sections D l hl E).mapDerivedCategory
  derived_normalized : ∀ P : CochainComplex
    (integralTowerModules l E (point D l hl).scheme) ℤ,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        (LisseRealization.sections D l hl E).mapDerivedCategory.map
          (pbcComplexCounit (scalar D l hl E a) P) ≫
        (LisseRealization.sections D l hl E).mapDerivedCategoryFactors.hom.app
          (rationalComplex D l hl E a P) =
      (pointModuleDerivedRationalization l E).map
        ((pointCompletedSections D.k l E).mapDerivedCategoryFactors.hom.app P) ≫
      (pointModuleRationalization l E).mapDerivedCategoryFactors.hom.app
        (((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  square : ∀ (K : Raw D l hl E (point D l hl))
    (hK : Lisse D l hl E (point D l hl) K),
    (fibreNormalization D l hl E K).hom ≫
      (DerivedCategory.homologyFunctor _ 0).map
        (derived.hom.app K.obj.obj ≫
          (LisseRealization.sections D l hl E).mapDerivedCategory.map
            (a.integral.inv.app K.obj)) ≫
      ((LisseRealization.sections D l hl E).mapDerivedCategoryHomologyFunctorIso 0).inv.app
        (a.J.obj K) = p.comparison.hom.app ⟨K, hK⟩


end WeilConjectures.LisseRealization
