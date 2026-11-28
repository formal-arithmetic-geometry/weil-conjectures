/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSquareMates
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
public import WeilConjectures.FourierTransform.FdCoefficientComparison
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarComplexCounitComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteRawScalarComparison

/-! # The ambient comparison fixed by the quotient-cocone equation

An ambient comparison between the integral scalar extension of finite coefficient stages and the
transported integral transition is determined by the quotient-cocone equation (chi) on good
complexes. If its ordinary scalar transport is fixed on the unit tensor generators, it is the
completion map, transported through the coefficient isomorphisms.

## Main statements

* `WeilConjectures.heq_tensorThroughCoefficientSquare_of_chi`: an ambient comparison satisfying
  chi is the completion map transported along the tensor comparison through the coefficient
  square.

## Implementation details

On a good complex, chi computes the comparison by the scalar-extension counit and the ordinary
transport; the counit description of the transported completion map
(`tensorThroughCoefficientSquare_inv_app_Q_of_tensorSection`) gives the same morphism. Every
integral constructible object is the localization of a good complex, a flat K-flat resolution.

The coefficient restrictions are taken along an arbitrary ring sheaf isomorphism equal to the
forgetful image of the coefficient isomorphism, so that the recorded restriction
`fdCoefficientTransport` can be substituted.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.8.2 and Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.LocallyFiniteAdicRealization

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] (T : Scheme.{u})

/-- The quotient-normalized coefficient isomorphisms intertwine the completed scalar map of the
finite coefficient stages with the completed coefficient map of the field inclusion. -/
theorem purCoefficientIso_hom_comp_completedCoefficientMap
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (WeilConjectures.purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom ≫
        WeilConjectures.completedCoefficientMap l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T =
      pbcCompletedScalarMap l Ω T h ≫
        (WeilConjectures.purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom := by
  rw [← WeilConjectures.scalarMap_eq_completed, WeilConjectures.coefficientScalar_square,
    rawScalar_coefficientMap]

end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {Ω : Type w} [Field Ω] [Algebra ℚ_[l] Ω] {T : Scheme.{u}}

attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- Restricted along any coefficient map, the completed scalar comparison on a good complex is
the scalar-extension counit followed by the completed chain comparison. -/
theorem pbcDerivedRestrict_map_completedTensorComparison_app
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (i : E →ₐ[ℚ_[l]] L)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ completedIntegralCommRingSheafUnrestricted l L T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    (pbcDerivedRestrict φ).map (pbcComplexCounit (completedCoefficientMap l E L i T) P.obj) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend (completedCoefficientMap l E L i T)).mapHomologicalComplex (.up ℤ)).obj
            P.obj) ≫
        DerivedCategory.Q.map (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map
          ((completedScalarChainComparison l E L i T).app P.obj)) =
      (pbcDerivedRestrict φ).map
          ((completedTensorComparison l T E L i).app (DerivedCategory.Q.obj P.obj)) ≫
        (pbcDerivedRestrict φ).map ((integralScalarExtensionComparison l E L i T).hom.app P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          ((integralScalarComplexFunctor l E L i T).obj P.obj) := by
  have hspec := (completedScalarComparison_existsUnique l E L i T).exists.choose_spec P
  rw [← IntegralFiniteExtension.pbcComplexCounit_eq_completedScalarCounit] at hspec
  have h1 : (pbcDerivedRestrict φ).map
        ((completedTensorComparison l T E L i).app (DerivedCategory.Q.obj P.obj)) ≫
        (pbcDerivedRestrict φ).map ((integralScalarExtensionComparison l E L i T).hom.app P) =
      (pbcDerivedRestrict φ).map (pbcComplexCounit (completedCoefficientMap l E L i T) P.obj) ≫
        (pbcDerivedRestrict φ).map
          (DerivedCategory.Q.map ((completedScalarChainComparison l E L i T).app P.obj)) := by
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ hspec).trans (Functor.map_comp _ _ _))
  have hn : (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend (completedCoefficientMap l E L i T)).mapHomologicalComplex (.up ℤ)).obj
            P.obj) ≫
        DerivedCategory.Q.map (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map
          ((completedScalarChainComparison l E L i T).app P.obj)) =
      (pbcDerivedRestrict φ).map
          (DerivedCategory.Q.map ((completedScalarChainComparison l E L i T).app P.obj)) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          ((integralScalarComplexFunctor l E L i T).obj P.obj) :=
    ((pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality
      ((completedScalarChainComparison l E L i T).app P.obj)).symm
  erw [hn, ← Category.assoc, ← h1, Category.assoc]

variable {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (e₀ : (adicLisseForget T).obj
        (pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E))) ≅
      (adicLisseForget T).obj
        (completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω E) T))
    (he₀ : (adicLisseForget T).mapIso (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T) = e₀)
    (e₁ : (adicLisseForget T).obj
        (pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω L))) ≅
      (adicLisseForget T).obj
        (completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω L) T))
    (he₁ : (adicLisseForget T).mapIso (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) = e₁)
    [h₀l : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} e₀.hom)]
    [h₀c : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} e₀.hom)]
    [h₁l : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} e₁.hom)]
    [h₁c : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} e₁.hom)]
    (o : completedOrdinaryScalarExtension l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) T ⋙ (SheafOfModules.restrictScalars.{u + 1} e₁.hom) ≅
      SheafOfModules.restrictScalars.{u + 1} e₀.hom ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h))
    (ho : ∀ (M : integralTowerModules.{u, u} l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
      (x : M.val.obj U),
      (o.hom.app M).val.app U (completedScalarTensorSection l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T M U 1 x) =
        pbcTensorSection (pbcCompletedScalarMap l Ω T h)
          ((SheafOfModules.restrictScalars.{u + 1} e₀.hom).obj M) U 1 x)
    (comparison : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
        (SheafOfModules.restrictScalars.{u + 1} e₀.hom).mapDerivedCategory ⋙
          pbcAmbientScalarExtension l Ω T h ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T ⋙
        (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
          (SheafOfModules.restrictScalars.{u + 1} e₁.hom).mapDerivedCategory)
    (chi : ∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T (DerivedCategory.Q.obj P.obj)),
      comparison.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
          (SheafOfModules.restrictScalars.{u + 1} e₁.hom).mapDerivedCategory.map
            ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
              (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
          (SheafOfModules.restrictScalars.{u + 1} e₁.hom).mapDerivedCategoryFactors.hom.app
            ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
              (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj) =
        (pbcAmbientScalarExtension l Ω T h).map
            ((SheafOfModules.restrictScalars.{u + 1} e₀.hom).mapDerivedCategoryFactors.hom.app
              P.obj) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((SheafOfModules.restrictScalars.{u + 1} e₀.hom).mapHomologicalComplex (.up ℤ)).obj
              P.obj) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.inv (.up ℤ)).app P.obj ≫
            ((SheafOfModules.restrictScalars.{u + 1} e₁.hom).mapHomologicalComplex (.up ℤ)).map
              ((completedScalarChainComparison l (pbcFiniteField.{u} l Ω E)
                (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).app P.obj)))

/-- On a good complex, the counit form of the quotient-cocone equation is the transported
completion map followed by the localization comparisons. -/
theorem ambientCounit_comp_completion_eq
    (o : pbcExtend (completedCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) T) ⋙
        pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom ≅
      pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h))
    (ho : ∀ (M : integralTowerModules.{u, u} l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
      (x : M.val.obj U),
      (o.hom.app M).val.app U (pbcTensorSection
        (completedCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T) M U 1 x) =
        pbcTensorSection (pbcCompletedScalarMap l Ω T h)
          ((pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom).obj M) U 1 x)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory) :
    (pbcAmbientScalarExtension l Ω T h).map
        ((Functor.mapDerivedCategoryFactors
          (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom)).hom.app
          P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        ((Functor.mapHomologicalComplex
          (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom)
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.inv (.up ℤ)).app P.obj ≫
        ((pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).mapHomologicalComplex
          (.up ℤ)).map ((completedScalarChainComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).app P.obj)) =
    ((tensorThroughCoefficientSquare T (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)
        (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) (pbcCompletedScalarMap l Ω T h)
        (completedCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T)
        (purCoefficientIso_hom_comp_completedCoefficientMap l Ω T h)).inv.app
          (DerivedCategory.Q.obj P.obj) ≫
      (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h)).app (DerivedCategory.Q.obj P.obj))) ≫
      (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (Functor.mapDerivedCategoryFactors
        (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom)).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj) := by
  have hsq := purCoefficientIso_hom_comp_completedCoefficientMap l Ω T h
  refine (congrArg (fun t ↦ _ ≫ _ ≫ t) (DerivedCategory.Q.map_comp _ _)).trans ?_
  refine (tensorThroughCoefficientSquare_inv_app_Q_of_tensorSection_assoc
    (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)
    (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) (pbcCompletedScalarMap l Ω T h)
    (completedCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T) hsq o ho P.obj _).symm.trans ?_
  refine (congrArg (fun t ↦ _ ≫ t)
    (pbcDerivedRestrict_map_completedTensorComparison_app (T := T) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
      (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom P)).trans ?_
  exact (Category.assoc _ _ _).symm

include he₀ he₁ ho chi in
/-- On a good complex, an ambient comparison satisfying chi is the transported completion map. -/
theorem heq_tensorThroughCoefficientSquare_of_chi_of_good
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T (DerivedCategory.Q.obj P.obj))
    (K₀ : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (hK : K₀ = ⟨DerivedCategory.Q.obj P.obj, hP⟩) :
    HEq (comparison.hom.app K₀)
      ((tensorThroughCoefficientSquare T (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)
          (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) (pbcCompletedScalarMap l Ω T h)
          (completedCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) T)
          (purCoefficientIso_hom_comp_completedCoefficientMap l Ω T h)).inv.app K₀.obj ≫
        (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
          ((completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h)).app K₀.obj)) := by
  subst he₀
  subst he₁
  subst hK
  apply heq_of_eq
  have hX : IsIso ((pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
      ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (Functor.mapDerivedCategoryFactors
        (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom)).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj)) := by
    have : IsIso ((pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P)) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso' this
      (Iso.isIso_hom ((Functor.mapDerivedCategoryFactors
        (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom)).app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj)))
  refine (cancel_mono
      ((pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
      ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (Functor.mapDerivedCategoryFactors
        (pbcRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom)).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))).1 ?_
  refine (chi P hP).trans ?_
  exact ambientCounit_comp_completion_eq h o ho P

include he₀ he₁ ho chi in
/-- An ambient comparison satisfying chi is the completion map, transported along the tensor
comparison through the coefficient square. -/
theorem heq_tensorThroughCoefficientSquare_of_chi
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    HEq (comparison.hom.app K)
      ((tensorThroughCoefficientSquare T (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)
          (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) (pbcCompletedScalarMap l Ω T h)
          (completedCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) T)
          (purCoefficientIso_hom_comp_completedCoefficientMap l Ω T h)).inv.app K.obj ≫
        (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
          ((completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h)).app K.obj)) := by
  have hgood :=
    heq_tensorThroughCoefficientSquare_of_chi_of_good h e₀ he₀ e₁ he₁ o ho comparison chi
  subst he₀
  subst he₁
  apply heq_of_eq
  have hsq := purCoefficientIso_hom_comp_completedCoefficientMap l Ω T h
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨P, s, hP, hflat, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω E) T)
    (DerivedCategory.Q.objPreimage K.obj)
  let P' : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory :=
    ⟨P, hP, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω E) T) (P.X i)).symm
      (hflat i)⟩
  have : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  let e : DerivedCategory.Q.obj P'.obj ≅ K.obj :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K.obj
  have hP' :
      sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T (DerivedCategory.Q.obj P'.obj) :=
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).prop_of_iso e.symm K.property
  let K₀ : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T :=
    ⟨DerivedCategory.Q.obj P'.obj, hP'⟩
  let fI : K₀ ≅ K := ObjectProperty.isoMk _ e
  have h0 := eq_of_heq (hgood P' hP' K₀ rfl)
  have hnat := comparison.hom.naturality fI.hom
  have n1 := (tensorThroughCoefficientSquare T (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)
    (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T) (pbcCompletedScalarMap l Ω T h)
    (completedCoefficientMap l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T) hsq).inv.naturality e.hom
  have n2 := (completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h)).naturality e.hom
  have n2' : (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h)).app K₀.obj) ≫
      (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((integralScalarExtensionOfUniverses l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T).map e.hom) =
      (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((pbcDerivedExtend (completedCoefficientMap l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T)).map e.hom) ≫
      (pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom).map
        ((completedTensorComparison l T (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h)).app K.obj) := by
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ n2.symm).trans (Functor.map_comp _ _ _))
  have hF : IsIso (((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      (SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).mapIso
          (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)).hom).mapDerivedCategory ⋙
      pbcAmbientScalarExtension l Ω T h).map fI.hom) := Functor.map_isIso _ _
  have hE : Epi (((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      (SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).mapIso
          (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)).hom).mapDerivedCategory ⋙
      pbcAmbientScalarExtension l Ω T h).map fI.hom) := IsIso.epi_of_iso _
  refine (cancel_epi (((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      (SheafOfModules.restrictScalars.{u + 1}
        ((adicLisseForget T).mapIso
          (purCoefficientIso l (pbcFiniteField.{u} l Ω E) T)).hom).mapDerivedCategory ⋙
      pbcAmbientScalarExtension l Ω T h).map fI.hom)).1 ?_
  refine hnat.trans ?_
  refine (congrArg (· ≫ _) h0).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) n2').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) n1.symm).trans ?_
  exact Category.assoc _ _ _

end WeilConjectures
