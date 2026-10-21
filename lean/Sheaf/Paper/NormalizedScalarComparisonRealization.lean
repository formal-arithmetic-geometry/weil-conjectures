/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CoefficientExtensionReductionModel
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence

import Sheaf.Algebra.Homology.ScalarInternalHomData
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralAmbientOperationModels
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.ScalarHomTensorComparison
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-! # Normalized realization of integral scalar comparisons

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
integral finite-reduction/common-stage clause; Stacks Tags 06YS, 0G7E, 07A4, 0941.
(blueprint: lem-pur-normalized-scalar-comparison-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Tensor realization is tested on every simultaneous quotient presentation, using
actual signed total tensor generators and the fixed K-injective Roos bridge.
Source: node statement, representative-normalization paragraph; Stacks 07A4, 0941
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def IsNormalizedScalarTensorRealization (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E W)
    (realization : integralCompletedTensor l E W ≅
      (S.reduction.prod S.reduction) ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W) :
    Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (d : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κ : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj C ≅ (unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
    (ξ : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj D ≅ (unrestrictedIntegralFiniteComplex l E W n).obj Q.obj),
    CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D d ξ →
    ∃ (hC : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (q : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D))).asFunctor ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)),
      (∀ (n : ℕ) (p s : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X s).val.obj (op (n, U.unop))),
        (((q.hom.app (op n)).f (p + s)).val.app U)
          (integralComparisonRestrictedSection l E W _ n U
            (coefficientTensorGenerator.{u, t + 1, t}
              (coefficientSequenceTopology (ProEt.topology W))
              (coefficientSequenceCommRingSheaf l E W) C D p s (p + s) rfl
              (op (n, U.unop)) x y)) =
          integralOperationsTotalTensorSection l E W n P.obj Q.obj p s U
            (((κ n).hom.f p).val.app U (coefficientEvaluationSection l E W _ n U x))
            (((ξ n).hom.f s).val.app U (coefficientEvaluationSection l E W _ n U y))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (coefficientSequenceLimit l E W).map (S.systemClosed.tensor.map
          (Prod.mkHom e.hom d.hom)) ≫
        (coefficientSequenceLimit l E W).map
          (S.systemTensorModel.iso (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) S.systemClosed C D hC hD).inv ≫
        (integralComparisonRoosBridge l E W ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralCompletedTensorComparison l E W).hom.app (P, Q)

/-- The specified completed tensor with its universal representative normalization.
Source: the integral/common-stage clause; Stacks 07A4, 0941
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
structure NormalizedScalarTensorRealization (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E W) where
  /-- Realizes the specified completed tensor on its ambient category. -/
  realization : integralCompletedTensor l E W ≅
    (S.reduction.prod S.reduction) ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W
  /-- All quotient presentations use the same signed tensor and Roos maps. -/
  normalization : IsNormalizedScalarTensorRealization l E W S ρ realization

/-- The strict system tensor functor, with the recorded signed total differential.
Source: Stacks 07A4 (blueprint: lem-pur-normalized-scalar-comparison-realization). -/
abbrev normalizedScalarSystemTotal (W : Scheme.{t}) :=
  coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

/-- Ordinary scalar extension on cochain systems, before localization.
Source: Stacks 06YY (blueprint: lem-pur-normalized-scalar-comparison-realization). -/
abbrev normalizedScalarSystemChain (W : Scheme.{t}) :=
  (integralComparisonSequenceScalarModel l E L ι W).E.mapHomologicalComplex (.up ℤ)

/-- Pure-tensor normalization for the ordinary comparison, including all total degrees.
Source: node statement and Stacks 07A4
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def IsNormalizedScalarTensorChain (W : Scheme.{t})
    (c : normalizedScalarSystemTotal l E W ⋙ normalizedScalarSystemChain l E L ι W ≅
      (normalizedScalarSystemChain l E L ι W).prod
        (normalizedScalarSystemChain l E L ι W) ⋙ normalizedScalarSystemTotal l L W) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf l L W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((c.hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection l E L ι W _ U b
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q (p + q) rfl U x y)) =
      coefficientTensorGenerator.{u, t + 1, t}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        ((normalizedScalarSystemChain l E L ι W).obj P)
        ((normalizedScalarSystemChain l E L ι W).obj Q) p q (p + q) rfl U
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) U b x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) U 1 y)

/-- Localization is fixed by the ordinary scalar counits and both K-flat tensor models.
Source: node statement, unique localization clause; Stacks 06YY, 07A4
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def IsNormalizedScalarTensorLocalization (W : Scheme.{t})
    (SE : CoefficientDerivedSystemCalculus l E W)
    (SL : CoefficientDerivedSystemCalculus l L W)
    (σ : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar l E L ι W ≅
      (integralComparisonDerivedSequenceScalar l E L ι W).prod
        (integralComparisonDerivedSequenceScalar l E L ι W) ⋙ SL.systemClosed.tensor) : Prop :=
  ∃ c : normalizedScalarSystemTotal l E W ⋙ normalizedScalarSystemChain l E L ι W ≅
      (normalizedScalarSystemChain l E L ι W).prod
        (normalizedScalarSystemChain l E L ι W) ⋙ normalizedScalarSystemTotal l L W,
    IsNormalizedScalarTensorChain l E L ι W c ∧
    ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) Q),
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) (Q.X i)) →
      ∃ (hSP : CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l L W)
          ((normalizedScalarSystemChain l E L ι W).obj P))
        (hSQ : CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l L W)
          ((normalizedScalarSystemChain l E L ι W).obj Q)),
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          (SE.systemTensorModel.iso (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) SE.systemClosed P Q hP hQ).hom ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          SL.systemClosed.tensor.map (Prod.mkHom
            ((integralComparisonSequenceScalarModel l E L ι W).ε.app P)
            ((integralComparisonSequenceScalarModel l E L ι W).ε.app Q)) =
        (integralComparisonSequenceScalarModel l E L ι W).ε.app
            ((normalizedScalarSystemTotal l E W).obj (P, Q)) ≫
          DerivedCategory.Q.map (c.hom.app (P, Q)) ≫
          (SL.systemTensorModel.iso (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l L W) SL.systemClosed
            ((normalizedScalarSystemChain l E L ι W).obj P)
            ((normalizedScalarSystemChain l E L ι W).obj Q) hSP hSQ).hom

/-- Reduction of a realized pullback, followed by the actual whole-system counit.
Source: node statement, definition of r_F
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
def normalizedScalarPullbackReduction {X Y : Scheme.{t}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (F : IntegralComparisonPullbackModel l E f SY ρ)
    (M : DerivedCategory (integralTowerModules l E Y)) :=
  SX.reduction.map (F.realization.hom.app M) ≫
    SX.adjunction.counit.app ((integralComparisonDerivedSequencePullback l E f).obj
      (SY.reduction.obj M))

/-- Reduction of a realized tensor, followed by the coherent counit.
Source: node statement, definition of r_T
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
def normalizedScalarTensorReduction (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E W)
    (T : NormalizedScalarTensorRealization l E W S ρ)
    (M N : DerivedCategory (integralTowerModules l E W)) :=
  S.reduction.map (T.realization.hom.app (M, N)) ≫
    S.adjunction.counit.app (S.systemClosed.tensor.obj (S.reduction.obj M, S.reduction.obj N))

/-- Reduction of a realized scalar change, followed by the L-coefficient counit.
Source: node statement, definition of r_S
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
def normalizedScalarExtensionReduction (W : Scheme.{t})
    (SE : CoefficientDerivedSystemCalculus l E W)
    (SL : CoefficientDerivedSystemCalculus l L W)
    (ρ : IntegralComparisonRoosModel l L W)
    (S : IntegralComparisonScalarModel l E L ι W SE ρ)
    (M : DerivedCategory (integralTowerModules l E W)) :=
  SL.reduction.map (S.realization.hom.app M) ≫
    SL.adjunction.counit.app
      ((integralComparisonDerivedSequenceScalar l E L ι W).obj (SE.reduction.obj M))

/-- K-flatness and flat terms of the actual finite coefficient complex.
This is only a conjunction of the existing predicates.
Source: Stacks 06YS, 0G7E (blueprint: lem-pur-normalized-scalar-comparison-realization). -/
def NormalizedScalarFiniteGood (W : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralOperationsFiniteModules l E W n) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P ∧
    SemilinearSections.flatTerms.{t + 1, t, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) P

/-- The coefficient ring at one of the four finite locations; true means L and X.
Source: node statement, W=X,Y and D=E,L
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
def normalizedScalarFiniteRing (X Y : Scheme.{t}) (n : ℕ) (b s : Bool) :
    Sheaf (ProEt.topology (if s then X else Y)) CommRingCat.{max u (t + 1)} :=
  if b then integralCoefficientCommRingSheaf l L (if s then X else Y) n
  else integralCoefficientCommRingSheaf l E (if s then X else Y) n

/-- The complex category at a specified finite coefficient and geometric location.
Source: node statement, finite-system representative clause
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
abbrev normalizedScalarFiniteComplexAt (X Y : Scheme.{t}) (n : ℕ) (b s : Bool) :=
  CochainComplex (SheafOfModules.{max u (t + 1)}
    ((sheafCompose (ProEt.topology (if s then X else Y))
      (forget₂ CommRingCat RingCat)).obj (normalizedScalarFiniteRing l E L X Y n b s))) ℤ

/-- Exactly the complexes obtained from the two quotient representatives by
scalar extension, finite pullback and signed total tensor, with any finite iteration.
Source: node statement, first paragraph
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
inductive NormalizedScalarGenerated {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P Q : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (b s : Bool) → normalizedScalarFiniteComplexAt l E L X Y n b s → Prop where
  | quotientP : NormalizedScalarGenerated f P Q n false false
      ((unrestrictedIntegralFiniteComplex l E Y n).obj P)
  | quotientQ : NormalizedScalarGenerated f P Q n false false
      ((unrestrictedIntegralFiniteComplex l E Y n).obj Q)
  | scalarY (A : CoefficientExtensionSystems l E L ι Y)
      (C : normalizedScalarFiniteComplexAt l E L X Y n false false) :
      NormalizedScalarGenerated f P Q n false false C →
      NormalizedScalarGenerated f P Q n true false
        (((A.levels n).model.E.mapHomologicalComplex (.up ℤ)).obj C)
  | scalarX (A : CoefficientExtensionSystems l E L ι X)
      (C : normalizedScalarFiniteComplexAt l E L X Y n false true) :
      NormalizedScalarGenerated f P Q n false true C →
      NormalizedScalarGenerated f P Q n true true
        (((A.levels n).model.E.mapHomologicalComplex (.up ℤ)).obj C)
  | pullE (C : normalizedScalarFiniteComplexAt l E L X Y n false false) :
      NormalizedScalarGenerated f P Q n false false C →
      NormalizedScalarGenerated f P Q n false true
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj C)
  | pullL (C : normalizedScalarFiniteComplexAt l E L X Y n true false) :
      NormalizedScalarGenerated f P Q n true false C →
      NormalizedScalarGenerated f P Q n true true
        (((integralOperationsLevelPullback l L f n).mapHomologicalComplex (.up ℤ)).obj C)
  | tensor (b s : Bool) (C D : normalizedScalarFiniteComplexAt l E L X Y n b s) :
      NormalizedScalarGenerated f P Q n b s C → NormalizedScalarGenerated f P Q n b s D →
      NormalizedScalarGenerated f P Q n b s
        ((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology (if s then X else Y))
          (normalizedScalarFiniteRing l E L X Y n b s)).obj (C, D))

/-- Every generated complex is flat-term K-flat, for all representatives of the
stated bounded constructible inputs. No boundedness of the representatives is imposed.
Source: node statement, first paragraph; Stacks 06YS, 0G7E, 07A2
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarRepresentativeClosure {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Prop :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory),
    Nonempty (DerivedCategory.Q.obj P.obj ≅ M.obj) →
    Nonempty (DerivedCategory.Q.obj Q.obj ≅ N.obj) →
    ∀ (n : ℕ) (b s : Bool) (C : normalizedScalarFiniteComplexAt l E L X Y n b s),
      NormalizedScalarGenerated l E L ι f P.obj Q.obj n b s C →
      CochainComplex.IsKFlatIndependentCoefficients
          (R := normalizedScalarFiniteRing l E L X Y n b s) C ∧
        SemilinearSections.flatTerms.{u + 1, u, u} (ProEt.topology (if s then X else Y))
          (normalizedScalarFiniteRing l E L X Y n b s) C

/-- Simultaneous representative-normalized realizations of the three operations.
The coefficient calculi are the recorded adjunctions, not newly chosen reductions.
Source: node statement, realization paragraph
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
structure NormalizedScalarOperationModels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (EX : CoefficientDerivedSystemCalculus l E X)
    (EY : CoefficientDerivedSystemCalculus l E Y)
    (LX : CoefficientDerivedSystemCalculus l L X)
    (LY : CoefficientDerivedSystemCalculus l L Y) where
  /-- Limit/Roos comparisons with the ordinary limit cone on K-injectives. -/
  roosEX : IntegralComparisonRoosModel l E X
  /-- The E-coefficient comparison over Y. -/
  roosEY : IntegralComparisonRoosModel l E Y
  /-- The L-coefficient comparison over X. -/
  roosLX : IntegralComparisonRoosModel l L X
  /-- The L-coefficient comparison over Y. -/
  roosLY : IntegralComparisonRoosModel l L Y
  /-- Pullback realizes the specified quotient pullback tower over E. -/
  pullE : IntegralComparisonPullbackModel l E f EY roosEX
  /-- Pullback realizes the specified quotient pullback tower over L. -/
  pullL : IntegralComparisonPullbackModel l L f LY roosLX
  /-- Scalar extension over X has the balanced-association normalization. -/
  scalarX : IntegralComparisonScalarModel l E L ι X EX roosLX
  /-- Scalar extension over Y has the balanced-association normalization. -/
  scalarY : IntegralComparisonScalarModel l E L ι Y EY roosLY
  /-- Tensor over E uses the signed total-tensor presentation. -/
  tensorE : NormalizedScalarTensorRealization l E Y EY roosEY
  /-- Tensor over L uses the same signed total-tensor convention. -/
  tensorL : NormalizedScalarTensorRealization l L Y LY roosLY
  /-- The entire-system derived scalar/tensor comparison. -/
  sigma : EY.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ≅
    (integralComparisonDerivedSequenceScalar l E L ι Y).prod
      (integralComparisonDerivedSequenceScalar l E L ι Y) ⋙ LY.systemClosed.tensor
  /-- The derived comparison localizes the ordinary scalar map on every representative. -/
  sigma_normalized : IsNormalizedScalarTensorLocalization l E L ι Y EY LY sigma
  /-- Its representative normalization determines it uniquely. -/
  sigma_unique : ∀ σ, IsNormalizedScalarTensorLocalization l E L ι Y EY LY σ → σ = sigma

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (EX : CoefficientDerivedSystemCalculus l E X)
  (EY : CoefficientDerivedSystemCalculus l E Y)
  (LX : CoefficientDerivedSystemCalculus l L X)
  (LY : CoefficientDerivedSystemCalculus l L Y)
  (D : NormalizedScalarOperationModels l E L ι f EX EY LX LY)

/-- The two reduction-coordinate equations are identities of whole-system arrows.
The completion hypotheses are conclusions for the indicated integral inputs.
Source: node statement, the two displayed equations
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarReductionEquations : Prop :=
  (∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj M.obj),
      LX.reduction.map (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        normalizedScalarPullbackReduction l L f LX LY D.roosLX D.pullL
          ((integralScalarExtension l E L ι Y).obj M.obj) ≫
        (integralComparisonDerivedSequencePullback l L f).map
          (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY M.obj) =
      normalizedScalarExtensionReduction l E L ι X EX LX D.roosLX D.scalarX
          ((integralDerivedPullback l E f).obj M.obj) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          (normalizedScalarPullbackReduction l E f EX EY D.roosEX D.pullE M.obj) ≫
        (integralComparisonSystemScalarPullback l E L ι f).hom.app (EY.reduction.obj M.obj)) ∧
  (∀ M N : sfIntegralConstructibleCategory l E Y,
    ∃ hT : IsSfDerivedComplete l E Y ((integralCompletedTensor l E Y).obj (M.obj, N.obj)),
      LY.reduction.map
          (scalarTensorCompleted l E L ι Y M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        normalizedScalarTensorReduction l L Y LY D.roosLY D.tensorL
          ((integralScalarExtension l E L ι Y).obj M.obj)
          ((integralScalarExtension l E L ι Y).obj N.obj) ≫
        LY.systemClosed.tensor.map (Prod.mkHom
          (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY M.obj)
          (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY N.obj)) =
      normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY
          ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        (integralComparisonDerivedSequenceScalar l E L ι Y).map
          (normalizedScalarTensorReduction l E Y EY D.roosEY D.tensorE M.obj N.obj) ≫
        D.sigma.hom.app (EY.reduction.obj M.obj, EY.reduction.obj N.obj))

/-- In normalized source and target coordinates the completed comparisons are
literally total limit applied to kappa and sigma, rather than just isomorphic objects.
Source: node statement, consequence paragraph
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarLimitEquations : Prop :=
  (∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj M.obj),
      (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        D.pullL.realization.hom.app ((integralScalarExtension l E L ι Y).obj M.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequencePullback l L f).map
            (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY M.obj)) =
      D.scalarX.realization.hom.app ((integralDerivedPullback l E f).obj M.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequenceScalar l E L ι X).map
            (normalizedScalarPullbackReduction l E f EX EY D.roosEX D.pullE M.obj)) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSystemScalarPullback l E L ι f).hom.app (EY.reduction.obj M.obj))) ∧
  (∀ M N : sfIntegralConstructibleCategory l E Y,
    ∃ hT : IsSfDerivedComplete l E Y ((integralCompletedTensor l E Y).obj (M.obj, N.obj)),
      (scalarTensorCompleted l E L ι Y M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        D.tensorL.realization.hom.app
          ((integralScalarExtension l E L ι Y).obj M.obj,
            (integralScalarExtension l E L ι Y).obj N.obj) ≫
        (coefficientSequenceLimit l L Y).map (LY.systemClosed.tensor.map (Prod.mkHom
          (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY M.obj)
          (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY N.obj))) =
      D.scalarY.realization.hom.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        (coefficientSequenceLimit l L Y).map
          ((integralComparisonDerivedSequenceScalar l E L ι Y).map
            (normalizedScalarTensorReduction l E Y EY D.roosEY D.tensorE M.obj N.obj)) ≫
        (coefficientSequenceLimit l L Y).map
          (D.sigma.hom.app (EY.reduction.obj M.obj, EY.reduction.obj N.obj)))

/-- Normalization survives the actual finite pullback, scalar and tensor operations.
Source: node statement and proof step 4, the quotient-adjoint associators
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarSystemPreservation : Prop :=
  (∀ A : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y A → IsNormalizedCoefficientSequence l E X
      ((integralComparisonDerivedSequencePullback l E f).obj A)) ∧
  (∀ A : coefficientSequenceDerived l L Y,
    IsNormalizedCoefficientSequence l L Y A → IsNormalizedCoefficientSequence l L X
      ((integralComparisonDerivedSequencePullback l L f).obj A)) ∧
  (∀ A B : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y A → IsNormalizedCoefficientSequence l E Y B →
      IsNormalizedCoefficientSequence l E Y (EY.systemClosed.tensor.obj (A, B))) ∧
  (∀ A B : coefficientSequenceDerived l L Y,
    IsNormalizedCoefficientSequence l L Y A → IsNormalizedCoefficientSequence l L Y B →
      IsNormalizedCoefficientSequence l L Y (LY.systemClosed.tensor.obj (A, B))) ∧
  (∀ A : coefficientSequenceDerived l E X,
    IsNormalizedCoefficientSequence l E X A → IsNormalizedCoefficientSequence l L X
      ((integralComparisonDerivedSequenceScalar l E L ι X).obj A)) ∧
  (∀ A : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y A → IsNormalizedCoefficientSequence l L Y
      ((integralComparisonDerivedSequenceScalar l E L ι Y).obj A))

/-- The reduction-coordinate maps are isomorphisms of whole coefficient systems.
Source: node statement, invertibility of r_F,r_T,r_S
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarReductionsInvertible : Prop :=
  (∀ M : DerivedCategory (integralTowerModules l E Y),
    IsIso (normalizedScalarPullbackReduction l E f EX EY D.roosEX D.pullE M)) ∧
  (∀ M : DerivedCategory (integralTowerModules l L Y),
    IsIso (normalizedScalarPullbackReduction l L f LX LY D.roosLX D.pullL M)) ∧
  (∀ M N : DerivedCategory (integralTowerModules l E Y),
    IsIso (normalizedScalarTensorReduction l E Y EY D.roosEY D.tensorE M N)) ∧
  (∀ M N : DerivedCategory (integralTowerModules l L Y),
    IsIso (normalizedScalarTensorReduction l L Y LY D.roosLY D.tensorL M N)) ∧
  (∀ M : DerivedCategory (integralTowerModules l E X),
    IsIso (normalizedScalarExtensionReduction l E L ι X EX LX D.roosLX D.scalarX M)) ∧
  (∀ M : DerivedCategory (integralTowerModules l E Y),
    IsIso (normalizedScalarExtensionReduction l E L ι Y EY LY D.roosLY D.scalarY M))

/-- Simultaneous quotient association retains the balanced coefficient formula,
insertion-of-one inverse, every strict transition and the actual coherent counit.
Source: node statement and coefficient-extension reduction model
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarQuotientAssociations : Prop :=
  (∀ A : CoefficientExtensionSystems l E L ι X,
    Nonempty (CoefficientExtensionReductionData l E L ι X EX LX A)) ∧
  (∀ A : CoefficientExtensionSystems l E L ι Y,
    Nonempty (CoefficientExtensionReductionData l E L ι Y EY LY A))

/-- Naturality of the specified completed comparison arrows, including arbitrary
morphisms of the integral inputs and both tensor arguments.
Source: node statement, final naturality assertion
(blueprint: lem-pur-normalized-scalar-comparison-realization). -/
@[irreducible] def NormalizedScalarComparisonNaturality : Prop :=
  (∀ (M M' : sfIntegralConstructibleCategory l E Y) (g : M ⟶ M')
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj M.obj))
    (hF' : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj M'.obj)),
    (integralScalarExtension l E L ι X).map ((integralDerivedPullback l E f).map g.hom) ≫
        (scalarPullbackCompleted l E L ι f M'.obj M'.property.1 hF').hom =
      (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        (integralDerivedPullback l L f).map ((integralScalarExtension l E L ι Y).map g.hom)) ∧
  (∀ (M M' N N' : sfIntegralConstructibleCategory l E Y) (g : M ⟶ M') (h : N ⟶ N')
    (hT : IsSfDerivedComplete l E Y ((integralCompletedTensor l E Y).obj (M.obj, N.obj)))
    (hT' : IsSfDerivedComplete l E Y ((integralCompletedTensor l E Y).obj (M'.obj, N'.obj))),
    (integralScalarExtension l E L ι Y).map
        ((integralCompletedTensor l E Y).map (Prod.mkHom g.hom h.hom)) ≫
        (scalarTensorCompleted l E L ι Y M'.obj N'.obj M'.property.1 N'.property.1 hT').hom =
      (scalarTensorCompleted l E L ι Y M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        (integralCompletedTensor l L Y).map (Prod.mkHom
          ((integralScalarExtension l E L ι Y).map g.hom)
          ((integralScalarExtension l E L ι Y).map h.hom)))

/-- Normalized realization of the specified scalar comparisons on entire quotient systems.
Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
integral finite-reduction/common-stage clause; Stacks 06YS, 0G7E, 07A4 and 0941.
(blueprint: lem-pur-normalized-scalar-comparison-realization).

Proof plan (the node's complete agent refinement):

1. Work with the strict semilinear system categories of [lem-coef-semilinear-derived-sections],
on fixed small presentations of the pro-etale topoi. Its scalar and tensor functors are
constructed on the derived category of the ringed sequence topos, and its geometric inverse image
is the whole-system inverse image. The constant-coefficient structure maps are the isomorphisms
of [prop-weil-pbc-proetale-constant-ring-map]. Naturality of the constant-sheaf construction
makes their squares with $i_n$ and every quotient map commute. Thus these are precisely the
finite $S_W,F_D,T_D$ in the statement, with their actual transitions. We will construct maps on
this category, retaining its coherent counit from [lem-coef-derived-system-evaluation-calculus].

2. The input resolutions exist by [lem-pc-kflat-resolution]. Apply
[lem-pur-kflat-change-of-rings] successively to $R_{E,Y}to A^E_{Y,n}to A^L_{Y,n}$, and
[lem-weil-pbc-ringed-topos-kflat-pullback] to each finite ringed-topos pullback. Apply
[lem-pur-kflat-total-tensor-model] whenever a signed direct-sum total tensor is taken. Each
conclusion gives both K-flatness and flatness of every term; its output therefore satisfies the
hypotheses for the next operation. This induction proves the asserted closure for all the
displayed models, including iterated operations and unbounded resolutions. No map of coefficient
rings is required to be flat.

3. The association map in the statement and its inverse are balanced: $((x a)otimes a')otimes b$
and $(xotimes aa')otimes b$ have the same image, and the second balancing relation is exactly
multiplication by $i_n(a')$. The inverse inserts $1$ in the $A^E_n$ factor. For $mge n$ the two
routes on $(xotimes a)otimes b$ give $xotimes q^L_{m,n}(i_m(a)b)=xotimes
i_n(q^E_{m,n}a)q^L_{m,n}b$. Consequently these are inverse chain maps of entire strict systems.
By [lem-pur-coefficient-extension-reduction-model] the resulting system
$(Potimes_{R_{E,Y}}A^L_{Y,n})_n$ is normalized and its coherent reduction comparison with
$widehat S_YM$ is the specified counit followed by inverse association. Apply the same statement
to $Q$ and to every ambient integral input that occurs below; it has no boundedness or
constructibility hypothesis.

4. The reduction $mathcal R_DK$ is normalized for every ambient $K$, and the actual
reconstruction counit is invertible on normalized systems, by
[lem-pur-normalized-actual-reconstruction-maps]. Finite pullback and tensor preserve
normalization: for a normalized $A$ the pullback transition-adjoint identifies with
$F_n(alpha^A_{m,n})$ under quotient/pullback association; for normalized $A,B$ the tensor
transition-adjoint identifies with $T_n(alpha^A_{m,n},alpha^B_{m,n})$ under quotient/tensor
association. These associations are the monoidal composition comparisons of
[lem-sfb-ringed-derived-monoidal-comparisons], applied also to scalar extension along the
quotient. Their naturality identifies the actual transition, by transposing its scalar-adjunction
unit. Both displayed maps are invertible. Scalar extension also preserves normalization: the
quotient-association comparison identifies its transition-adjoint with $S_n(alpha^A_{m,n})$. Thus
all intermediate finite systems used in the two equations are normalized, including the
reductions of the integral operation inputs.

5. Let $rho_F,rho_T$ denote the natural functor identifications supplied by
[lem-pur-completed-primitive-counit-comparison]. These realize the specified $widehat F_D,widehat
T_D$ as $mathcal L_DF_Dmathcal R_D$ and $mathcal L_DT_D(mathcal R_D,mathcal R_D)$ with their
actual quotient representatives. For scalar extension, association from Step 3 identifies the
defining restricted Roos tower of [def-weil-integral-scalar-extension] with $U_LSmathcal R_E$.
Apply the natural comparison of [lem-weil-strict-roos-comparison] to obtain $rho_S:widehat
Sxrightarrow{sim}mathcal L_LSmathcal R_E$. Exactness of countable products needed here holds by
[lem-weil-proetale-countable-products-exact]. That comparison is normalized on K-injective tower
resolutions by the ordinary limit cone, with zero shifted coordinate, and respects strict
augmentations. Thus all three realizations have precisely the representative and total-limit
normalization required in the statement.

6. Define $r_H=e_{Hmathcal R(-)}mathcal R(rho_H)$ for $H=F,T,S$, with the indicated coefficient
on each reduction. For $T$ there are two input reductions. These are whole-system maps by
[lem-coef-derived-system-evaluation-calculus]. Steps 3--4 put the systems on their right in the
normalized subcategory. Hence $e$ is invertible by
[lem-pur-normalized-actual-reconstruction-maps], and $rho_H$ is invertible by Step 5; all the
$r_H$ are isomorphisms. On scalar-extension inputs this is exactly the coherent counit comparison
of [lem-pur-coefficient-extension-reduction-model], by its stated formula and the association
used to define $rho_S$.

7. On the ringed sequence topos the simultaneous chain maps $kappa,sigma$ are those of
[lem-pur-strict-coefficient-comparison-calculus], for $R^0=A^E$, $R^1=A^L$ (take $R^2=R^1$ if a
three-stage package is desired). Its formulas and inverse formulas are maps of strict systems,
with both differential summands and every transition. Use the actual normalized scalar adjunction
of [lem-pur-sheaf-ring-derived-coefficient-adjunction] and the canonical derived tensor
representative model of [lem-weil-pbc-site-derived-tensor-descent]. Apply
[lem-sfb-scalar-tensor-comparison] on this sequence site: its full representative square is
exactly the localization of $sigma$ with the universal scalar counits and K-flat tensor model
comparisons, as packaged in [def-sfb-scalar-hom-comparison-data]. For $kappa$, the ordinary
scalar-association maps descend by the composition and geometric-isomorphism comparisons of
[lem-sfb-ringed-derived-monoidal-comparisons]. All these are isomorphisms on derived system
categories. Uniqueness of the tensor localization is [lem-weil-pbc-site-derived-tensor-descent]
on the same ringed site; the pullback localization is unique by
[lem-weil-pbc-localization-universal-property] on the resolving presentation. This constructs the
specified $sigma^D,kappa^D$, rather than trying to lift arbitrary evaluated arrows.

8. For the pullback equation set $A_F=S_XF_Emathcal R_EM$ and $B_F=F_LS_Ymathcal R_EM$, and
define $$beta_{A_F}=mathcal L_LS_X(r_{F,E}),rho_{S,X},qquad beta_{B_F}=mathcal
L_LF_L(r_{S,Y}),rho_{F,L}.$$ Their domains are respectively $widehat S_Xwidehat F_EM$ and
$widehat F_Lwidehat S_YM$. For tensor set $A_T=ST_E(mathcal R_EM,mathcal R_EN)$,
$B_T=T_L(Smathcal R_EM,Smathcal R_EN)$, with $$beta_{A_T}=mathcal L_LS(r_{T,E}),rho_S,qquad
beta_{B_T}=mathcal L_LT_L(r_S,r_S),rho_{T,L}.$$ All are isomorphisms. Write $c_H,d_H$ for the
right-side and left-side reduction-coordinate composites before $mathcal R_L(a_H)$ in the
question. Naturality of the whole-system counit of [lem-coef-derived-system-evaluation-calculus]
gives $$c_H=e_{A_H}mathcal R_L(beta_{A_H}),qquad d_H=e_{B_H}mathcal R_L(beta_{B_H})quad(H=F,T).$$
For example $e_{S_XF_Emathcal R_EM}mathcal R_Lmathcal L_LS_X(r_{F,E})=S_X(r_{F,E})e_{S_Xmathcal
R_Ewidehat F_EM}$. This proves the coordinate identity in the system category.

9. We will use the actual reduction-adjunction unit, including its augmentation normalization. In
[lem-coef-sequence-projection-derived-adjunction], the Hom bijection is the derived fraction
extension of the ordinary tensor/limit correspondence. For a flat-term K-flat $V$, resolve its
strict quotient system by $q:mathcal R Vto I$ on the sequence site. The identity of $mathcal RV$
is represented by $q$. The ordinary adjunction sends $q$ to the chain map $Vtolim I$ given by
$vmapsto(q_n(votimes1))_n$; this is the derived unit under that Hom bijection. The
right-derived-limit identification of [lem-coef-sequence-pushforward-limit-projections]
transports this same adjunction to $mathcal Rdashvmathcal L$. By the strict-augmentation
normalization in [lem-weil-strict-roos-comparison], the quotient product map with zero shifted
coordinate gives the same map after the resolution and the ordinary-limit inclusion. Thus $u_V$
is precisely the strict quotient augmentation in the specified total-limit/Roos coordinates. This
comparison uses the ordinary derived-adjunction correspondence on a resolution, not faithfulness
of evaluations.

10. Put $alpha_F=kappa^D_{mathcal R_EM}$, $alpha_T=sigma^D_{mathcal R_EM,mathcal R_EN}$ and
construct $$a_H^0=beta_{B_H}^{-1}mathcal L_L(alpha_H)beta_{A_H}quad(H=F,T).$$ These are natural
isomorphisms of the actual completed-operation words. We now verify their canonical
tensor-association normalization; this is needed to identify their arrows with $a_F,a_T$, not
merely their objects. Use [lem-pur-integral-ambient-operation-models] to write the underlying
integral pullback or tensor as $C_EU$, where $C_D=mathcal L_Dmathcal R_D$, $U=F^{rm amb}_EM$ or
$U=Motimes^L_{R_E}N$. Its identification respects the actual quotient augmentation $u_U:Uto
C_EU$. Write $B_W=-otimes^L_{R_{E,W}}R_{L,W}$ for ambient scalar change. On complete inputs the
actual comparison $chi:B_WKtowidehat S_WK$ is the quotient-augmentation isomorphism of
[lem-weil-finite-free-completed-scalar-comparison]. Consequently the augmentation into the source
word is $$nu_H:B_WUxrightarrow{B_W(u_U)}B_WC_EUxrightarrow{chi_{C_EU}}widehat S_WC_EU.$$ Here
$W=X$ for pullback and $W=Y$ for tensor; $C_EU$ is complete by Step 4 and reconstruction.

11. The source coordinate $beta_{A_H}$ identifies $nu_H$ with the canonical completion unit of
$B_WU$. To check the map, use one flat-term K-flat representative $V$ of $U$. The entire
reduction system of $B_WU$ is represented by $((Votimes_{R_E}R_L)otimes_{R_L}A^L_n)_n$,
identified with $(Votimes_{R_E}A^L_n)_n$ by multiplying the coefficient factors. Likewise
$Smathcal R_EU$ is represented by $((Votimes_{R_E}A^E_n)otimes_{A^E_n}A^L_n)_n$, with the same
association. Both strict augmentations take $votimes b$ to $(votimesbar b)_n$ and have zero
shifted Roos coordinate. The normalization of $chi$ in
[lem-weil-finite-free-completed-scalar-comparison] uses exactly this strict augmentation. The
inserted $u_U$ cancels the counit in $r_H$ by $e_{mathcal R_EU}mathcal R_E(u_U)=1$ of
[lem-coef-derived-system-evaluation-calculus]; the ambient model comparison preserves that
augmentation. Thus the assertion is an identity of strict augmentations followed by total-limit
functoriality, using [lem-weil-strict-roos-comparison], not a deduction from equal evaluated
maps.

12. For the target word use $chi_M,chi_N$ to replace $widehat S$ of the complete inputs by
ambient $B$; then [lem-pur-integral-ambient-operation-models] identifies that target with
$C_LV_H$, where $V_F=F_L^{rm amb}B_YM$ and $V_T=B_YMotimes^L_{R_{L,Y}}B_YN$. The ambient
coefficient comparisons $$b_F:B_XF_E^{rm amb}Mxrightarrow{sim}F_L^{rm amb}B_YM,qquad
b_T:B_Y(Motimes^L_{R_{E,Y}}N)xrightarrow{sim}B_YMotimes^L_{R_{L,Y}}B_YN$$ are the canonical
composition and tensor maps of [lem-sfb-ringed-derived-monoidal-comparisons]. Reducing $b_H$ on
simultaneous K-flat models gives precisely $alpha_H$, under the associations in Step 11: for
pullback both routes multiply the coefficient factors and insert $1$; for tensor both send
$(xotimes y)otimes b$ to $(xotimes b)otimes(yotimes1)$. Differentiating gives the same two
summands with $(-1)^{deg x}$, and quotienting the coefficients before or after these formulas
gives the same result. These are the strict maps of
[lem-pur-strict-coefficient-comparison-calculus]. Naturality of the Roos comparison and the
representative normalization of $chi$ therefore show $$a_H^0nu_H=u_{V_H}b_H$$ in these target
coordinates, as an equality obtained from the strict augmented towers.

13. The canonical tensor-association normalization of the integral scalar comparisons of
[lem-pur-integral-operations-scalar-extension] means extending the ambient $b_H$ to the completed
words with the quotient units: in the coordinates above it is the equation $a_Hnu_H=u_{V_H}b_H$.
It specifies a unique arrow. Indeed [lem-pur-normalized-reconstruction-adjunction-calculus] gives
an adjoint equivalence between complete objects and normalized systems;
[lem-pur-normalized-actual-reconstruction-maps] says that $mathcal R_LZ$ is normalized for every
ambient $Z$. The adjunction consequently makes $u_Z:Zto C_LZ$ a reflection into complete objects:
for complete $J$, precomposition gives $operatorname{Hom}(C_LZ,J)congoperatorname{Hom}(Z,J)$.
This also follows directly by applying $mathcal R_Ldashvmathcal L_L$ and the inverse of $u_J$.
Step 11 identifies $nu_H$ with this unit, and the target $C_LV_H$ is complete. Step 12 proves
that $a_H^0$ has the required normalization. Thus it is precisely the representative-normalized
choice $a_H$ in the statement. This argument supplies and fixes that normalization of the
existence isomorphisms; no normalization is inferred from the mere existence assertion of the
cited scalar-extension theorem.

14. For $H=F,T$, substitute $a_H=beta_{B_H}^{-1}mathcal L_L(alpha_H)beta_{A_H}$ into Step 8.
Naturality of the actual counit [lem-coef-derived-system-evaluation-calculus] gives $$d_Hmathcal
R_L(a_H)=e_{B_H}mathcal R_Lmathcal L_L(alpha_H)mathcal R_L(beta_{A_H})=alpha_H e_{A_H}mathcal
R_L(beta_{A_H})=alpha_Hc_H.$$ Expanding $c_F,d_F,c_T,d_T$ yields exactly the two equations in the
question. All terms are morphisms in the derived category of whole systems, so all evaluations
and transitions follow by functoriality. Applying $mathcal L_L$ and the same inverse source and
target coordinates gives the asserted integral-limit descriptions.

15. Every comparison used above is natural on the simultaneous K-flat models and preserves their
quasi-isomorphism comparisons. Scalar and tensor localization and uniqueness from
[lem-weil-pbc-site-derived-tensor-descent] and [lem-weil-pbc-localization-universal-property]
therefore give naturality for all input morphisms and independence from resolutions through their
canonical comparisons. The total-limit comparison [lem-weil-strict-roos-comparison] is itself
natural and independent of its K-injective tower resolution. Thus the same statements hold for
the actual completed maps. In Steps 3, 7, 10 and 11, quotient scalar changes were computed on
K-flat inputs; their ring maps were never assumed flat. Limits were applied to already
constructed strict system maps, and no operation was commuted with an arbitrary inverse limit.
-/
theorem normalizedScalarComparisonRealization
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤))) :
    NormalizedScalarRepresentativeClosure l E L ι f ∧
    NormalizedScalarSystemPreservation l E L ι f EY LY ∧
    NormalizedScalarQuotientAssociations l E L ι EX EY LX LY ∧
    NormalizedScalarComparisonNaturality l E L ι f ∧
    ∃ D : NormalizedScalarOperationModels l E L ι f EX EY LX LY,
      NormalizedScalarReductionsInvertible l E L ι f EX EY LX LY D ∧
      NormalizedScalarReductionEquations l E L ι f EX EY LX LY D ∧
      NormalizedScalarLimitEquations l E L ι f EX EY LX LY D := by
  sorry

end WeilConjectures
