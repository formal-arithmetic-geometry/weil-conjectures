/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.CategoryTheory.ClosedScalarHomComparison
public import Sheaf.Paper.CoefficientHomZeroClass

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

/-- The internal scalar comparison on zeroth derived sections is the external scalar
adjunction, for every complex and without a flatness assumption on the coefficient map.
Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08J9 and 08JA
(blueprint: lem-coef-scalar-hom-zero-compatibility).

Proof: choose flat-term K-flat representatives for P and M, and a K-injective
representative for N. Represent h followed by k by a chain map into the restricted
K-injective representative, replacing its target further when computing internal Hom.
The specified zero-cycle identification sends its Hom cocycle to this derived map
with the inverse resolution augmentation. Uncurry the inverse representing scalar-Hom
comparison. Its five defining bijections give ordinary evaluation followed by the
scalar transpose. On each total-tensor summand, the tensor model square and its pure
formula identify this map with the scalar extension of that chain map: a generator
x tensor y is sent to the evaluation on x and y, and the scalar unit sends x to
1 tensor x. The scalar representative transpose equation identifies the resulting
chain map with the prescribed derived scalar transpose. No sign occurs in degree
zero. The ordinary section formulas and both derived unit equations carry the same
cocycle through the sections comparisons. Consequently its image under the target
zero-cycle identification is the scalar adjunct of h followed by k. Naturality in
both inputs and invariance under the chosen K-flat and K-injective resolution
isomorphisms prove the formula for arbitrary derived objects. The uniqueness clauses
of the normalized zero-cycle equivalences remove the representative choices. -/
theorem scalarHomZeroCompatibility
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
    (P M : D.{c, v, max c v r} J R) (N : D.{c, v, max c v r} J S)
    (k : M ⟶ (resD φ).obj N) (h : P ⟶ M) :
    coefficientHomZeroEquiv.{r, c, v} J S (σ.T.obj P) N
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
          (pR.functor.map
              ((internalHom.{c, v, r} J R).map (Prod.mkHom (𝟙 (op P)) k) ≫
                (ClosedScalarHom.component a b σ.adjunction ν P N).inv) ≫
            γ.inv.app ((internalHom.{c, v, r} J S).obj (op (σ.T.obj P), N))) ≫
          ξS.hom.app ((internalHom.{c, v, r} J S).obj (op (σ.T.obj P), N)))
        (ξR.inv.app ((internalHom.{c, v, r} J R).obj (op P, M))
          ((coefficientHomZeroEquiv.{r, c, v} J R P M).symm h))) =
      (σ.adjunction.homEquiv P N).symm (h ≫ k) := by
  sorry

end SheafOfModules.ScalarHomZero
