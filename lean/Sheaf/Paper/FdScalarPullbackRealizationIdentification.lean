module

public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FdPullbackComparison
import Sheaf.Paper.FdPullbackAugmentationCounitMatching
public import Sheaf.Paper.PullbackCommonStrictTowerModels
public import Sheaf.Paper.SpecifiedPullbackComparisonAlpha
public import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport
import Sheaf.CategoryTheory.FiniteFreeCompletionTransport
import Sheaf.Paper.KFlatScalarComparisonNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import Sheaf.CategoryTheory.StrictProjectionLimitData

import Sheaf.TraceFormula.CounitRealizationSubstitution
import Sheaf.TraceFormula.IntegralComparisonCounitCharacterization
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # Identification of scalar pullback realization maps

Source: blueprint, trace-definition coefficient-category identification;
Stacks Tags 0941 and 099N(5)
(blueprint: lem-fd-scalar-pullback-realization-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Reassemble a strict diagram of complexes without changing any transition.
Source: Stacks 0941, strict diagrams of complexes
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarTowerComplex {A : Type a} [Category.{v} A] [Abelian A] :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  obj Q :=
    { X := fun i ↦ Q ⋙ HomologicalComplex.eval A (.up ℤ) i
      d := fun i j ↦
        { app := fun n ↦ (Q.obj n).d i j
          naturality := fun _ _ f ↦ (Q.map f).comm i j }
      shape := fun i j hij ↦ NatTrans.ext (funext (fun n ↦ (Q.obj n).shape i j hij))
      d_comp_d' := fun i j k _ _ ↦ NatTrans.ext (funext (fun n ↦ (Q.obj n).d_comp_d i j k)) }
  map f :=
    { f := fun i ↦
        { app := fun n ↦ (f.app n).f i
          naturality := fun _ _ g ↦ congrArg (fun c ↦ c.f i) (f.naturality g) }
      comm' := fun i j _ ↦ NatTrans.ext (funext (fun n ↦ (f.app n).comm i j)) }
  map_id _Q := HomologicalComplex.hom_ext _ _ (fun _i ↦ NatTrans.ext (funext (fun _n ↦ rfl)))
  map_comp _f _g :=
    HomologicalComplex.hom_ext _ _ (fun _i ↦ NatTrans.ext (funext (fun _n ↦ rfl)))

/-- Finite-limit preservation by the actual tower scalar functor.
Source: finite-free strict-tower transport, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
instance fdScalarTowerLimits (W : Scheme.{u}) :
    PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) (integralOrdinaryScalar l E L ι W)) :=
  ⟨fun _ _ _ ↦ CategoryTheory.whiskeringRight_preservesLimitsOfShape _⟩

/-- Finite-colimit preservation by the actual tower scalar functor.
Source: finite-free strict-tower transport, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
instance fdScalarTowerColimits (W : Scheme.{u}) :
    PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) (integralOrdinaryScalar l E L ι W)) :=
  ⟨fun _ _ _ ↦ CategoryTheory.whiskeringRight_preservesColimitsOfShape _⟩

/-- Exact scalar change on the whole strict tower category.
Source: Stacks 0941, finite-free tensor/limit transport
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarTower (W : Scheme.{u}) :=
  (projectionPost (I := ℕᵒᵖ) (integralOrdinaryScalar l E L ι W)).mapDerivedCategory

/-- The constant-tower square induced by the literal ordinary scalar square.
Source: Stacks 0941, constant-tower/limit adjunction
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarConstantSquare (W : Scheme.{u}) :
    integralComparisonConstantTower l E W ⋙ fdScalarTower l E L ι W ≅
      integralOrdinaryDerivedScalar l E L ι W ⋙ integralComparisonConstantTower l L W :=
  Functor.mapDerivedCategoryCompNatIso
      (F := Functor.const ℕᵒᵖ) (G := projectionPost (I := ℕᵒᵖ)
        (integralOrdinaryScalar l E L ι W))
      (Functor.compConstIso (J := ℕᵒᵖ) (integralOrdinaryScalar l E L ι W)).symm ≪≫
    (Functor.mapDerivedCategoryCompNatIso
      (F := integralOrdinaryScalar l E L ι W) (G := Functor.const ℕᵒᵖ)
      (Iso.refl _)).symm

/-- The canonical tensor/derived-limit comparison, defined as the adjunct of
scalar change of the entire-tower counit. It contains no selected basis.
Source: Stacks 0941, finite-free strict-tower transport
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarLimitComparison (W : Scheme.{u})
    (Q : coefficientSequenceRestrictedDerived l E W) :
    (integralOrdinaryDerivedScalar l E L ι W).obj
        ((coefficientConstantTowerLimit l E W).obj Q) ⟶
      (coefficientConstantTowerLimit l L W).obj ((fdScalarTower l E L ι W).obj Q) :=
  (integralComparisonConstantAdjunction l L W).homEquiv _ _
    ((fdScalarConstantSquare l E L ι W).inv.app
        ((coefficientConstantTowerLimit l E W).obj Q) ≫
      (fdScalarTower l E L ι W).map ((integralComparisonTowerCounit l E W).app Q))

/-- The ordinary scalar square on complexes, using the literal module isomorphism.
Source: trace-definition coefficient transport, Stacks 03EL
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarTransportComplex (W : Scheme.{u})
    (c : integralOrdinaryScalar l E L ι W ⋙ fdCoefficientTransport l L W ≅
      fdCoefficientTransport l E W ⋙ pbcExtend (pbcScalarCoefficientMap l E L ι W))
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    ((fdCoefficientTransport l L W).mapHomologicalComplex (.up ℤ)).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ)).obj
        (((fdCoefficientTransport l E W).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := c.hom.app (P.X i)
  comm' i j _ := (c.hom.naturality (P.d i j)).symm

/-- Canonical coefficient-identity transport of ordinary scalar extension.
The module map is fixed on sheafified tensor generators, and the derived map is
fixed by the actual universal cochain counit. These are presentation identifications.
Source: trace-definition final coefficient-category identification
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
structure FdScalarCoefficientTransport (W : Scheme.{u}) where
  moduleIso : integralOrdinaryScalar l E L ι W ⋙ fdCoefficientTransport l L W ≅
    fdCoefficientTransport l E W ⋙ pbcExtend (pbcScalarCoefficientMap l E L ι W)
  generators : ∀ (M : integralTowerModules l E W) (V : W.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj V)
    (x : M.val.obj V),
    (moduleIso.hom.app M).val.app V (integralOrdinaryTensorSection l E L ι W M V s x) =
      pbcTensorSection (pbcScalarCoefficientMap l E L ι W)
        ((fdCoefficientTransport l E W).obj M) V
        ((integralDetailedCoefficientComparison W l L).inv.hom.app V s) x
  derivedIso : integralOrdinaryDerivedScalar l E L ι W ⋙ integralDetailedTransport W l L ≅
    integralDetailedTransport W l E ⋙ pbcEmbeddingAmbientTensor l E L ι W
  normalization : ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
    derivedIso.hom.app (DerivedCategory.Q.obj P) ≫
      (pbcEmbeddingAmbientTensor l E L ι W).map
        ((fdCoefficientTransportFactors l E W).hom.app P) ≫
      pbcComplexCounit (pbcScalarCoefficientMap l E L ι W)
        (((fdCoefficientTransport l E W).mapHomologicalComplex (.up ℤ)).obj P) =
      (integralDetailedTransport W l L).map
        ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P) ≫
      (fdCoefficientTransportFactors l L W).hom.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (fdScalarTransportComplex l E L ι W moduleIso P)

/-- The specified entire strict scalar map d, now as a complex of diagrams.
Source: the quotient generator formula and actual transitions of the scalar comparison
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarStrictMap {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ((projectionPost (I := ℕᵒᵖ) (integralOrdinaryScalar l E L ι U)).mapHomologicalComplex
      (.up ℤ)).obj
        (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l E h).obj P)) ⟶
      fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l L h).obj
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P)) :=
  fdScalarTowerComplex.map ((scalarPullbackTower l E L ι h).app P)

/-- Delta-p on the strict representatives: normalized rho-E, the canonical finite-free
limit comparison, Rlim(d) for the entire tower, and normalized rho-L.
Source: Stacks 0941, trace-definition scalar normalization
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarLimitOnTowers (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (integralOrdinaryDerivedScalar l E L ι U).obj
      (DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l E h).obj P)) ⟶
    DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor l L h).obj
      (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (integralOrdinaryDerivedScalar l E L ι U).map
      (((D.coefficient E).roos U).comparison.inv.app
        (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l E h).obj P))) ≫
    fdScalarLimitComparison l E L ι U
      (DerivedCategory.Q.obj
        (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l E h).obj P))) ≫
    (coefficientConstantTowerLimit l L U).map
      ((projectionPost (I := ℕᵒᵖ)
          (integralOrdinaryScalar l E L ι U)).mapDerivedCategoryFactors.hom.app
          (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l E h).obj P))) ≫
    (coefficientConstantTowerLimit l L U).map
      (DerivedCategory.Q.map (fdScalarStrictMap l E L ι h P)) ≫
    ((D.coefficient L).roos U).comparison.hom.app
      (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l L h).obj
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P)))

/-- The Rlim(d) realization on every flat-term K-flat representative, including
all defining localization comparisons. No replacement or resolution is selected.
Source: trace-definition scalar normalization, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarLimitRealization (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι U).obj
      ((integralDerivedPullback l E h).obj (DerivedCategory.Q.obj P.obj)) ⟶
    (integralDerivedPullback l L h).obj
      ((integralOrdinaryDerivedScalar l E L ι T).obj (DerivedCategory.Q.obj P.obj)) :=
  (integralOrdinaryDerivedScalar l E L ι U).map
      ((integralDerivedPullbackComparison l E h).hom.app P) ≫
    fdScalarLimitOnTowers l E L ι D h P.obj ≫
    (integralDerivedPullbackComparison l L h).inv.app
      ⟨_, scalarGood l E L ι T P⟩ ≫
    (integralDerivedPullback l L h).map
      ((integralOrdinaryScalar l E L ι T).mapDerivedCategoryFactors.inv.app P.obj)

/-- The same Rlim(d) arrow at an object with a specified good presentation.
Source: trace-definition scalar normalization, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarLimitAt (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : DerivedCategory (integralTowerModules l E T))
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) :
    (integralOrdinaryDerivedScalar l E L ι U).obj ((integralDerivedPullback l E h).obj K) ⟶
    (integralDerivedPullback l L h).obj ((integralOrdinaryDerivedScalar l E L ι T).obj K) :=
  (integralOrdinaryDerivedScalar l E L ι U).map
      ((integralDerivedPullback l E h).map e.inv) ≫
    fdScalarLimitRealization l E L ι D h P ≫
    (integralDerivedPullback l L h).map
      ((integralOrdinaryDerivedScalar l E L ι T).map e.hom)

/-- The actual PBC comparison, in the orientation C Fp-E to Fp-L C and with
only the specified coefficient-identity transports inserted.
Source: PBC scalar extension, trace-definition coefficient identification
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarActualPbc {U T : Scheme.{u}} (h : U ≅ T)
    (cU : FdScalarCoefficientTransport l E L ι U)
    (cT : FdScalarCoefficientTransport l E L ι T)
    (bE : FdCommonStrictTowerModels l E h)
    (K : sfIntegralConstructibleCategory l E T) :
    (integralDetailedTransport U l L).obj
        ((integralOrdinaryDerivedScalar l E L ι U).obj
          ((integralDerivedPullback l E h.hom).obj K.obj)) ⟶
      (pbcActualCompletedPull h.hom (pbcIntegralDatum l L)).obj
        ((integralDetailedTransport T l L).obj
          ((integralOrdinaryDerivedScalar l E L ι T).obj K.obj)) :=
  cU.derivedIso.hom.app ((integralDerivedPullback l E h.hom).obj K.obj) ≫
    (pbcEmbeddingAmbientTensor l E L ι U).map (bE.actual_ambient.hom.app K) ≫
    (pbcScalarCompletedPullIso l E L ι h.hom).inv.app
      ((integralDetailedTransport T l E).obj K.obj) ≫
    (pbcActualCompletedPull h.hom (pbcIntegralDatum l L)).map
      (cT.derivedIso.inv.app K.obj)

/-- A whole-tower adjunct, retaining tower homotopies. The source map can in
particular be lambda chi or mu F(chi) delta. This is the actual constant/Rlim
adjunction, followed by the fixed quotient-system restriction, not evaluations.
Source: Stacks 0941, trace-definition scalar normalization
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarWholeAdjunct (U : Scheme.{u})
    {A : DerivedCategory (integralTowerModules l L U)}
    {B : coefficientSequenceDerived l L U}
    (f : A ⟶ (coefficientSequenceLimit l L U).obj B) :=
  ((integralComparisonConstantAdjunction l L U).homEquiv _ _).symm f

/-- The fixed reduction target of both scalar/pullback routes, before total limit.
Source: trace-definition scalar normalization, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarReductionTarget (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : DerivedCategory (integralTowerModules l E T)) : coefficientSequenceDerived l L U :=
  (integralComparisonDerivedSequenceScalar l E L ι U).obj
    ((integralComparisonDerivedSequencePullback l E h).obj
      (((D.coefficient E).system T).reduction.obj K))

/-- Present the reduction target using only reduction, exact system pullback and
its localization comparison, the universal scalar cochain counit, and a strict
coefficient presentation. In particular neither lambda nor mu occurs here.
Source: trace-definition scalar normalization, Stacks 06YY and 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarTargetComparison (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E T) ℤ)
    (eC : ((D.coefficient E).system T).reduction.obj
      (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (q : ((coefficientSequenceRestriction l L U).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequenceScalarModel l E L ι U).E).mapHomologicalComplex
        (.up ℤ)).obj
          (((integralComparisonSequencePullback l E h).mapHomologicalComplex
            (.up ℤ)).obj C)) ≅
      fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l L h).obj
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P.obj))) :
    (coefficientSequenceDerivedRestriction l L U).obj
      (fdScalarReductionTarget l E L ι D h (DerivedCategory.Q.obj P.obj)) ⟶
    DerivedCategory.Q.obj
      (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l L h).obj
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P.obj))) :=
  (coefficientSequenceDerivedRestriction l L U).map
    ((integralComparisonDerivedSequenceScalar l E L ι U).map
      ((integralComparisonDerivedSequencePullback l E h).map eC.hom) ≫
    (integralComparisonDerivedSequenceScalar l E L ι U).map
      ((integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom.app C) ≫
    (integralComparisonSequenceScalarModel l E L ι U).ε.app
      (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C)) ≫
  (coefficientSequenceRestriction l L U).mapDerivedCategoryFactors.hom.app _ ≫
  DerivedCategory.Q.map q.hom

/-- A simultaneous presentation of the fixed reduction target. The reduction
comparison retains every horizontal transition. The strict target identification
is pinned on local scalar/pullback tensor generators, with the specified d_m on
its right side; it is not an arbitrary isomorphism of the target objects.
Source: trace-definition scalar normalization; Stacks 06YY, 099N(5), 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
structure FdScalarTargetPresentation (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) where
  reductionComplex : CochainComplex (coefficientSequenceModules l E T) ℤ
  reductionIso : ((D.coefficient E).system T).reduction.obj
    (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj reductionComplex
  quotients : ∀ n : ℕ,
    ((coefficientSequenceEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj
      reductionComplex ≅ (unrestrictedIntegralFiniteComplex l E T n).obj P.obj
  reduction_normalization : CoefficientReductionPresentation l E T
    ((D.coefficient E).system T).toCoefficientDerivedSystemReduction
      P.obj P.property.1 reductionComplex reductionIso quotients
  towerIso : ((coefficientSequenceRestriction l L U).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequenceScalarModel l E L ι U).E).mapHomologicalComplex
        (.up ℤ)).obj
          (((integralComparisonSequencePullback l E h).mapHomologicalComplex
            (.up ℤ)).obj reductionComplex)) ≅
    fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l L h).obj
      (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P.obj))
  generators : ∀ (n : ℕ) (i : ℤ) (V : T.ProEt)
    (s : (completedIntegralCommRingSheafUnrestricted l L U).obj.obj
      (op ((proEtaleBaseChange h).obj V)))
    (x : (reductionComplex.X i).val.obj (op (n, V))),
    (((towerIso.hom.f i).app (op n)).val.app
      (op ((proEtaleBaseChange h).obj V)))
        (integralComparisonRestrictedSection l L U
          ((integralComparisonSequenceScalarModel l E L ι U).E.obj
            ((integralComparisonSequencePullback l E h).obj (reductionComplex.X i))) n
          (op ((proEtaleBaseChange h).obj V))
          (integralComparisonSequenceTensorSection l E L ι U
            ((integralComparisonSequencePullback l E h).obj (reductionComplex.X i))
            (op (n, (proEtaleBaseChange h).obj V))
            ((completedIntegralCommRingProjectionUnrestricted l L U n).hom.app
              (op ((proEtaleBaseChange h).obj V)) s)
            (integralComparisonSequenceGenerator l E h (reductionComplex.X i) n V x))) =
      ((((scalarPullbackTower l E L ι h).app P.obj).app (op n)).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
        (integralOrdinaryTensorSection l E L ι U
          ((((integralOperationsPullbackTowerFunctor l E h).obj P.obj).obj (op n)).X i)
          (op ((proEtaleBaseChange h).obj V)) s
          (integralOperationsPullbackGenerator l E h n
            (((unrestrictedIntegralFiniteComplex l E T n).obj P.obj).X i) V
            (((quotients n).hom.f i).val.app (op V)
              (coefficientEvaluationSection l E T (reductionComplex.X i) n (op V) x))))
  source_iota_zero : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E U) ℤ)
    (i j : ℤ) (hij : i + -1 = j),
    (integralComparisonLimitToRoos l E U I).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary I.asFunctor)).v i j hij = 0
  comparison_isIso : IsIso
    (fdScalarTargetComparison l E L ι D h P reductionComplex reductionIso towerIso)

/-- The shared whole-tower augmentation, constructed directly into the system's
reduction target. First take the normalized source Roos counit (its unshifted
quotient projections), scalar-extend it, and apply the actual strict d. Finally
insert the inverse of the cochain-counit comparison of the specified target
presentation. The source iota uses the limit tuple and zero shifted coordinate.
No scalar completion map, lambda, mu, or scalar/pullback derived comparison is
used in this definition. All arrows are in the derived category of entire towers.
Source: trace-definition scalar normalization, Stacks 0941
(blueprint: lem-fd-scalar-pullback-realization-identification). -/
def fdScalarAugmentedRealization (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} (h : U ⟶ T) (K : sfIntegralConstructibleCategory l E T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (M : FdScalarTargetPresentation l E L ι D h P) :
    (integralComparisonConstantTower l L U).obj
      ((integralOrdinaryDerivedScalar l E L ι U).obj
        ((integralDerivedPullback l E h).obj K.obj)) ⟶
    (coefficientSequenceDerivedRestriction l L U).obj
      (fdScalarReductionTarget l E L ι D h K.obj) :=
  letI := M.comparison_isIso
  (integralComparisonConstantTower l L U).map
    ((integralOrdinaryDerivedScalar l E L ι U).map
      ((integralDerivedPullback l E h).map e.inv ≫
        (integralDerivedPullbackComparison l E h).hom.app P)) ≫
  (fdScalarConstantSquare l E L ι U).inv.app _ ≫
  (fdScalarTower l E L ι U).map
    ((integralComparisonConstantTower l E U).map
      (((D.coefficient E).roos U).comparison.inv.app
        (fdScalarTowerComplex.obj ((integralOperationsPullbackTowerFunctor l E h).obj P.obj))) ≫
      (integralComparisonTowerCounit l E U).app _) ≫
  (projectionPost (I := ℕᵒᵖ)
    (integralOrdinaryScalar l E L ι U)).mapDerivedCategoryFactors.hom.app _ ≫
  DerivedCategory.Q.map (fdScalarStrictMap l E L ι h P.obj) ≫
  inv (fdScalarTargetComparison l E L ι D h P M.reductionComplex M.reductionIso M.towerIso) ≫
  (coefficientSequenceDerivedRestriction l L U).map
    ((integralComparisonDerivedSequenceScalar l E L ι U).map
      ((integralComparisonDerivedSequencePullback l E h).map
        (((D.coefficient E).system T).reduction.map e.hom)))

/-- Identification of the two actual scalar/pullback maps, including the PBC
ordinary mate and completion units, and the fixed framework lambda/mu realization.
Source: trace-definition coefficient-category identification; Stacks 0941 and 099N(5)
(blueprint: lem-fd-scalar-pullback-realization-identification).

Proof (the node's eight steps):
1. Use common strict towers and their quotient-normalized coefficient identities.
   Finite freeness and exact countable products allow normalized strict Roos comparison
   and finite-free transport of entire augmented towers. Scalar change preserves good
   representatives (specifiedPullbackComparisonAlpha).
2. On local generators the inverse balanced-tensor mate sends x tensor s to the same
   inverse-image generator. Substituting the two coefficient units in the prescribed
   d-m formula proves d C(gamma-E) = gamma-L theta as an entire augmented tower map.
   Use kflat_scalar_comparison_normalization and fdPullbackAugmentationCounitMatching.
3. Apply the canonical tensor/limit augmentation identity, then Rlim(d). Normalized
   rho carries (0,gamma) to the derived-limit augmentation, giving the unit equation.
4. The image of the source uniformizer is a unit times a positive power of the target
   uniformizer (the DVR theorem). finiteFreeCompletionTransport carries C(kappa-E)
   to a completion unit; its Hom bijection gives the cancellation assertion below.
5. The reflected coefficient square identifies the PBC comparison as completion of
   the actual ordinary mate followed by unit-normalized completion transport. It has
   the same unit equation. Cancel by step 4 to identify delta-p with that actual map.
6. specifiedPullbackComparisonAlpha identifies alpha-s with chi inverse, the diagonal
   two-coordinate Roos map, and F(chi). The fixed simultaneous realization system's
   lambda uses scalar change of the whole counit, not isolated finite evaluations.
7. Present the fixed target S_seq F_seq reduction(K) by reduction of P. Exact
   sequence pullback and the universal scalar cochain counit give the comparison
   fdScalarTargetComparison. On tensor generators its strict coefficient isomorphism
   is pinned by d_m and the quotient identifications; flatness of P, rather than of
   the quotient ring map, makes this comparison invertible. This gives a target
   presentation, for every good P. Every such presentation has the same formula.
   Define fdScalarAugmentedRealization by the source Roos counit, scalar change,
   d, and the inverse of that comparison, directly into the restricted target.
   The source iota has zero shifted coordinate, stated by source_iota_zero.
   Substitute the zero-shifted-coordinate scalar unit in both whole-tower adjuncts.
   In the mu route the reduction/realization counit cancels reduction of the unit by
   the triangle identity (counitRealizationSubstitution). Both adjuncts are therefore
   equal to this independently constructed unshifted-projection/d augmentation,
   for every normalized target presentation. Cancel mu and chi to obtain alpha-s
   = lambda followed by mu inverse.
8. All constructions are natural derived transformations. The representative formula
   holds for every good presentation, so descends independently of resolutions and
   restricts through the common full integral constructible categories. Only completion
   units and realization isomorphisms are cancelled; no d-m is inverted and no finite
   quotient ring map is assumed flat. This includes equality of coefficient fields.
-/
theorem fdScalarPullbackRealizationIdentification
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E₀ L₀ : Padic.FiniteCoefficientFields l Ω) (ι₀ : E₀ ≤ L₀)
    (D : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (h : U ≅ T) :
    ∃ (cU : FdScalarCoefficientTransport l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
      (pbcFiniteFieldInclusion l Ω ι₀) U)
      (cT : FdScalarCoefficientTransport l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
        (pbcFiniteFieldInclusion l Ω ι₀) T),
      (∀ (J : PbcCompletedDerived T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E₀)))
        (_hJ : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E₀)) J),
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
          (pbcFiniteFieldInclusion l Ω ι₀) U).map
            ((pbcActualCompletedPullUnit h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω
              E₀))).app J) ≫
          (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
            (pbcFiniteFieldInclusion l Ω ι₀) h.hom).inv.app J =
        (pbcScalarOrdinaryPullIso l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
          (pbcFiniteFieldInclusion l Ω ι₀) h.hom).inv.app J ≫
          (pbcActualCompletedPullUnit h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω L₀))).app
            ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
              (pbcFiniteFieldInclusion l Ω ι₀) T).obj J)) ∧
      (∀ (J : PbcCompletedDerived T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E₀)))
        (_hJ : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E₀)) J)
        (a b : (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
          L₀) (pbcFiniteFieldInclusion l Ω ι₀) U).obj
          ((pbcActualCompletedPull h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E₀))).obj J) ⟶
          (pbcActualCompletedPull h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω L₀))).obj
            ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
              (pbcFiniteFieldInclusion l Ω ι₀) T).obj J)),
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
          (pbcFiniteFieldInclusion l Ω ι₀) U).map
            ((pbcActualCompletedPullUnit h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω
              E₀))).app J) ≫ a =
          (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
            (pbcFiniteFieldInclusion l Ω ι₀) U).map
            ((pbcActualCompletedPullUnit h.hom (pbcIntegralDatum l (pbcFiniteField.{u} l Ω
              E₀))).app J) ≫ b → a = b) ∧
      ∀ (bE : FdCommonStrictTowerModels l (pbcFiniteField.{u} l Ω E₀) h) (bL :
        FdCommonStrictTowerModels l (pbcFiniteField.{u} l Ω L₀) h)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E₀) T),
        ∃ (hF : IsSfDerivedComplete l (pbcFiniteField.{u} l Ω E₀) U ((integralDerivedPullback l
          (pbcFiniteField.{u} l Ω E₀) h.hom).obj K.obj))
          (hC : sfIntegralConstructible l (pbcFiniteField.{u} l Ω L₀) T
            ((integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
              L₀) (pbcFiniteFieldInclusion l Ω ι₀) T).obj K.obj)),
          (scalarPullbackCompleted l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
            (pbcFiniteFieldInclusion l Ω ι₀) h.hom K.obj K.property.1 hF).hom =
            (integralComparisonLambda l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
              (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K).hom ≫
              (integralComparisonMu l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K).inv ∧
          ∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E₀) T).FullSubcategory)
            (e : DerivedCategory.Q.obj P.obj ≅ K.obj),
            fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
              (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K.obj P e =
              (scalarPullbackOrdinary l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                (pbcFiniteFieldInclusion l Ω ι₀) h.hom).hom.app K.obj ∧
            ((integralDetailedTransport U l (pbcFiniteField.{u} l Ω L₀)).map
                (fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                  (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K.obj P e) ≫
              bL.actual_ambient.hom.app
                ⟨(integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u}
                  l Ω L₀) (pbcFiniteFieldInclusion l Ω ι₀) T).obj K.obj, hC⟩ =
              fdScalarActualPbc l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                (pbcFiniteFieldInclusion l Ω ι₀) h cU cT bE K) ∧
            (Nonempty (FdScalarTargetPresentation l (pbcFiniteField.{u} l Ω E₀)
                (pbcFiniteField.{u} l Ω L₀) (pbcFiniteFieldInclusion l Ω ι₀) D h.hom P) ∧
              ∀ M : FdScalarTargetPresentation l (pbcFiniteField.{u} l Ω E₀)
                (pbcFiniteField.{u} l Ω L₀) (pbcFiniteFieldInclusion l Ω ι₀) D h.hom P,
            (fdScalarWholeAdjunct l (pbcFiniteField.{u} l Ω L₀) U
                ((scalarCompletionIso l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                  (pbcFiniteFieldInclusion l Ω ι₀) U _ hF).hom ≫
                  (integralComparisonLambda l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
                    L₀) (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K).hom) =
              fdScalarAugmentedRealization l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
                L₀) (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K P e M) ∧
            (fdScalarWholeAdjunct l (pbcFiniteField.{u} l Ω L₀) U
                ((scalarPullbackOrdinary l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                  (pbcFiniteFieldInclusion l Ω ι₀) h.hom).hom.app K.obj ≫
                  (integralDerivedPullback l (pbcFiniteField.{u} l Ω L₀) h.hom).map
                    (scalarCompletionIso l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                      (pbcFiniteFieldInclusion l Ω ι₀) T K.obj K.property.1).hom ≫
                  (integralComparisonMu l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                    (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K).hom) =
              fdScalarAugmentedRealization l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
                L₀) (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K P e M)) ∧
            (∀ (P' : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E₀)
              T).FullSubcategory)
              (e' : DerivedCategory.Q.obj P'.obj ≅ K.obj),
              fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K.obj P e =
                fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                  (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K.obj P' e') ∧
            (∀ (K' : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E₀) T)
              (P' : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E₀) T).FullSubcategory)
              (e' : DerivedCategory.Q.obj P'.obj ≅ K'.obj) (a : K ⟶ K'),
              (integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω
                L₀) (pbcFiniteFieldInclusion l Ω ι₀) U).map
                  ((integralDerivedPullback l (pbcFiniteField.{u} l Ω E₀) h.hom).map a.hom) ≫
                fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                  (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K'.obj P' e' =
              fdScalarLimitAt l (pbcFiniteField.{u} l Ω E₀) (pbcFiniteField.{u} l Ω L₀)
                (pbcFiniteFieldInclusion l Ω ι₀) D h.hom K.obj P e ≫
                (integralDerivedPullback l (pbcFiniteField.{u} l Ω L₀) h.hom).map
                  ((integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E₀)
                    (pbcFiniteField.{u} l Ω L₀) (pbcFiniteFieldInclusion l Ω ι₀) T).map
                      a.hom)) := by
  sorry

end WeilConjectures
