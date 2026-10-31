/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoefficientSequenceGlobalSections
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.ClosedScalarHomComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientHomZeroClass

/-! # Degree-zero normalization of the scalar internal-Hom adjunction

The scalar adjunction and its tensor comparison act on the canonical zero-cycle
identification by the external scalar transpose. This statement concerns a single
coefficient map and has no sequence, projection, or inverse-limit input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections


namespace SheafOfModules.ScalarHomZero

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify J AddCommGrpCat.{max c v r}]

/-- The scalar-Hom zero-cycle formula on chosen complex representatives.
Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08J9 and 08JA
(blueprint: lem-coef-scalar-hom-zero-compatibility-on-q).

This is the representative stage of the proof; resolution descent is recorded
separately. -/
def scalarHomZeroCompatibility_onQ_statement
    (R S : Sheaf J CommRingCat.{max c v r}) (φ : R ⟶ S)
    (σ : ScalarData.{c, v, max c v r} φ)
    (a : SemilinearSections.Closed.{c, v, r} J R) (b : SemilinearSections.Closed.{c, v, r} J S)
    (am : Models.{c, v, r} J R a) (bm : Models.{c, v, r} J S b)
    (ν : a.tensor ⋙ σ.T ≅ (σ.T.prod σ.T) ⋙ b.tensor)
    (_hm : ScalarTensorComparisonModel.{c, v, r} J R S φ σ a b am bm ν)
    (pR : SequenceSectionsDerivedPair (sequenceCoefficientSections R))
    (pS : SequenceSectionsDerivedPair (sequenceCoefficientSections S))
    (oR : sequenceCoefficientSections R ≅ coefficientOrdinarySections.{r, c, v} J R)
    (oS : sequenceCoefficientSections S ≅ coefficientOrdinarySections.{r, c, v} J S)
    (_hoR : ∀ (M : sequenceCoefficientModules R) (x : (sequenceCoefficientSections R).obj M)
      (U : Cᵒᵖ), (M.unitHomEquiv (oR.hom.app M x)).val U =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J R) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x)
    (_hoS : ∀ (M : sequenceCoefficientModules S) (x : (sequenceCoefficientSections S).obj M)
      (U : Cᵒᵖ), (M.unitHomEquiv (oS.hom.app M x)).val U =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J S) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x)
    (ξR : pR.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J R)
    (ξS : pS.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J S)
    (_hξR : ∀ (I : CochainComplex (sequenceCoefficientModules R) ℤ), I.IsKInjective →
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (pR.unit.app I) ≫
          ξR.hom.app (DerivedCategory.Q.obj I) =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex oR (.up ℤ)).hom.app I) ≫
            coefficientSiteSectionsComparison.{r, c, v} J R I))
    (_hξS : ∀ (I : CochainComplex (sequenceCoefficientModules S) ℤ), I.IsKInjective →
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (pS.unit.app I) ≫
          ξS.hom.app (DerivedCategory.Q.obj I) =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex oS (.up ℤ)).hom.app I) ≫
            coefficientSiteSectionsComparison.{r, c, v} J S I))
    (γ : pS.functor ≅ resD φ ⋙ pR.functor)
    (_hγ : ∀ K : CochainComplex (sequenceCoefficientModules S) ℤ,
      pS.unit.app K ≫ γ.hom.app (DerivedCategory.Q.obj K) ≫
          pR.functor.map ((sequenceCoefficientRestriction φ).mapDerivedCategoryFactors.hom.app K) =
        pR.unit.app (((sequenceCoefficientRestriction φ).mapHomologicalComplex (.up ℤ)).obj K))
    (L₀ M₀ : CochainComplex (sequenceCoefficientModules R) ℤ)
    (N₀ : CochainComplex (sequenceCoefficientModules S) ℤ)
    (k : DerivedCategory.Q.obj M₀ ⟶ (resD φ).obj (DerivedCategory.Q.obj N₀))
    (h : DerivedCategory.Q.obj L₀ ⟶ DerivedCategory.Q.obj M₀) : Prop := by
  exact
    coefficientHomZeroEquiv.{r, c, v} J S
      (σ.T.obj (DerivedCategory.Q.obj L₀)) (DerivedCategory.Q.obj N₀)
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (pR.functor.map
              ((internalHom.{c, v, r} J R).map
                (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj L₀))) k) ≫
                (ClosedScalarHom.component a b σ.adjunction ν
                  (DerivedCategory.Q.obj L₀) (DerivedCategory.Q.obj N₀)).inv) ≫
            γ.inv.app ((internalHom.{c, v, r} J S).obj
              (op (σ.T.obj (DerivedCategory.Q.obj L₀)), DerivedCategory.Q.obj N₀))) ≫
          ξS.hom.app ((internalHom.{c, v, r} J S).obj
            (op (σ.T.obj (DerivedCategory.Q.obj L₀)), DerivedCategory.Q.obj N₀)))
        (ξR.inv.app ((internalHom.{c, v, r} J R).obj
          (op (DerivedCategory.Q.obj L₀), DerivedCategory.Q.obj M₀))
          ((coefficientHomZeroEquiv.{r, c, v} J R (DerivedCategory.Q.obj L₀)
            (DerivedCategory.Q.obj M₀)).symm h))) =
      (σ.adjunction.homEquiv (DerivedCategory.Q.obj L₀)
        (DerivedCategory.Q.obj N₀)).symm (h ≫ k)

/-- The normalized scalar-Hom compatibility on direct complex representatives.
Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08J9 and 08JA.
The representative tensor-Hom square and the section comparison equations identify
the zero-cycle image with the scalar adjunct.
(blueprint: lem-coef-scalar-hom-zero-compatibility-on-q) -/
theorem scalarHomZeroCompatibility_onQ
    (R S : Sheaf J CommRingCat.{max c v r}) (φ : R ⟶ S)
    (σ : ScalarData.{c, v, max c v r} φ)
    (a : SemilinearSections.Closed.{c, v, r} J R) (b : SemilinearSections.Closed.{c, v, r} J S)
    (am : Models.{c, v, r} J R a) (bm : Models.{c, v, r} J S b)
    (ν : a.tensor ⋙ σ.T ≅ (σ.T.prod σ.T) ⋙ b.tensor)
    (hm : ScalarTensorComparisonModel.{c, v, r} J R S φ σ a b am bm ν)
    (pR : SequenceSectionsDerivedPair (sequenceCoefficientSections R))
    (pS : SequenceSectionsDerivedPair (sequenceCoefficientSections S))
    (oR : sequenceCoefficientSections R ≅ coefficientOrdinarySections.{r, c, v} J R)
    (oS : sequenceCoefficientSections S ≅ coefficientOrdinarySections.{r, c, v} J S)
    (hoR : ∀ (M : sequenceCoefficientModules R) (x : (sequenceCoefficientSections R).obj M)
      (U : Cᵒᵖ), (M.unitHomEquiv (oR.hom.app M x)).val U =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J R) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x)
    (hoS : ∀ (M : sequenceCoefficientModules S) (x : (sequenceCoefficientSections S).obj M)
      (U : Cᵒᵖ), (M.unitHomEquiv (oS.hom.app M x)).val U =
        (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J S) ⋙
          sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x)
    (ξR : pR.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J R)
    (ξS : pS.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J S)
    (hξR : ∀ (I : CochainComplex (sequenceCoefficientModules R) ℤ), I.IsKInjective →
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (pR.unit.app I) ≫
          ξR.hom.app (DerivedCategory.Q.obj I) =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex oR (.up ℤ)).hom.app I) ≫
            coefficientSiteSectionsComparison.{r, c, v} J R I))
    (hξS : ∀ (I : CochainComplex (sequenceCoefficientModules S) ℤ), I.IsKInjective →
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (pS.unit.app I) ≫
          ξS.hom.app (DerivedCategory.Q.obj I) =
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex oS (.up ℤ)).hom.app I) ≫
            coefficientSiteSectionsComparison.{r, c, v} J S I))
    (γ : pS.functor ≅ resD φ ⋙ pR.functor)
    (hγ : ∀ K : CochainComplex (sequenceCoefficientModules S) ℤ,
      pS.unit.app K ≫ γ.hom.app (DerivedCategory.Q.obj K) ≫
          pR.functor.map ((sequenceCoefficientRestriction φ).mapDerivedCategoryFactors.hom.app K) =
        pR.unit.app (((sequenceCoefficientRestriction φ).mapHomologicalComplex (.up ℤ)).obj K))
    (L₀ M₀ : CochainComplex (sequenceCoefficientModules R) ℤ)
    (N₀ : CochainComplex (sequenceCoefficientModules S) ℤ)
    (k : DerivedCategory.Q.obj M₀ ⟶ (resD φ).obj (DerivedCategory.Q.obj N₀))
    (h : DerivedCategory.Q.obj L₀ ⟶ DerivedCategory.Q.obj M₀) :
    scalarHomZeroCompatibility_onQ_statement J R S φ σ a b am bm ν hm pR pS oR oS
      hoR hoS ξR ξS hξR hξS γ hγ L₀ M₀ N₀ k h := by
  sorry


end SheafOfModules.ScalarHomZero
