/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
/-! # Interfaces for coherent finite reduction of coefficient extension

Source: the integral-operations clause of the main-20261015 blueprint.
The model records and their predicates are shared by the construction lemmas and
the public reduction theorem. Existing declarations are moved here verbatim.
(blueprint: stage3-pur-extension-reduction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section ScalarZero
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{r} C] {R S : Sheaf J CommRingCat.{r}} {f : R ⟶ S}
end ScalarZero

section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)

/-- The actual comparison: inverse of the completed-limit identification, followed
by the coherent counit. Associativity and unitors only display its functorial type.
Source: node proof step 4, φ=a⁻¹e, expressed with C already associated
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom

/-- Apply ordinary scalar association degree by degree. The explicit zero-map
instances expose the existing additive witnesses without changing any functor.
Source: integral operations, node proof step 2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (((scalarReductionExtension l E W n ⋙ (A.levels n).model.E).mapHomologicalComplex
      (.up ℤ)).obj P) ⟶
      (((integralScalarReduction l E L ι W n).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P

/-- The existing shifted Roos cone's actual nth projection, with its tower explicit.
Source: integral operations and completed scalar extension, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n

/-- The finite evaluation equation of the coherent representative model.
Caching this proposition prevents expansion when projecting the model record.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def IsCoefficientExtensionModelEvaluation
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
      (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
        (A.levels n).model.ε.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj)

/-- The completion identification preserves the specified Roos projections.
Caching this proposition prevents expansion when projecting the model record.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def IsCoefficientExtensionCompletionProjection
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    completion.inv.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceProjection l L W n).app
          ((coefficientExtensionSystem l E L ι W SE A).obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        DerivedCategory.Q.map
          (coefficientExtensionRoosProjection l E L ι W P.obj n)

/-- The natural isomorphism of coherent quotient systems, with its specified counit.
Source: integral operations, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso

end WeilConjectures
