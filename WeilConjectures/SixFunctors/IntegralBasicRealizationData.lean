/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemExpressionDomain
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction

public import WeilConjectures.SixFunctors.IntegralSystemCanonicalBridge
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerFunctorSpec

/-! # Primitive integral realization with strict coefficient towers

Source: blueprint main-20261015, fix-prop-coherence.proof.md, primitive coefficient
comparisons; the five-step refinement in the DAG
(blueprint: def-sf-integral-basic-realization-data).

Only primitive operations occur here. Each domain below is the specialization of
Expression.domain to one operation and its inputs. Natural number n denotes the
positive exponent n+1 throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The input and output conditions of Expression.domain for one unary operation.
Source: fix-prop-coherence, intermediate-domain paragraph
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnaryDomain (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y) :
    ObjectProperty (Integral l E X) := fun K ↦
  sfIntegralConstructible l E X K ∧
    Good l E X ((calculus l E X).reduction.obj K) ∧
    Good l E Y (A.obj ((calculus l E X).reduction.obj K))

/-- Both inputs and the tensor output satisfy the recorded intermediate domain.
Source: fix-prop-coherence, two-input tensor clause
(blueprint: def-sf-integral-basic-realization-data). -/
def basicTensorDomain (W : Scheme.{u}) : ObjectProperty (Integral l E W × Integral l E W) :=
  fun K ↦ sfIntegralConstructible l E W K.1 ∧ sfIntegralConstructible l E W K.2 ∧
    Good l E W ((calculus l E W).reduction.obj K.1) ∧
    Good l E W ((calculus l E W).reduction.obj K.2) ∧
    Good l E W ((calculus l E W).systemClosed.tensor.obj
      ((calculus l E W).reduction.obj K.1, (calculus l E W).reduction.obj K.2))

/-- The compactification domain also retains the intermediate open-extension bound.
Source: fix-prop-coherence, chosen compactification paragraph
(blueprint: def-sf-integral-basic-realization-data). -/
def basicSupportDomain (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : ObjectProperty (Integral l E X) := fun K ↦
  basicUnaryDomain l E X Y (Operations.shriek l E o c.i ⋙ Operations.push l E o c.g) K ∧
    Good l E c.Z ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))

/-- Inclusion of the primitive support domain into the recorded integral category.
Source: fix-prop-coherence, compact-support comparison domain
(blueprint: def-sf-integral-basic-realization-data). -/
def basicSupportInput (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (basicSupportDomain l E o c).FullSubcategory ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1.1)

/-- Restrict a primitive operation's actual reduction/system/limit composite.
Source: fix-prop-coherence, displayed d_A
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnarySource (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y) :=
  (basicUnaryDomain l E X Y A).ι ⋙ (calculus l E X).reduction ⋙ A ⋙
    coefficientSequenceLimit l E Y

/-- Restrict the prescribed integral operation to the same full input domain.
Source: fix-prop-coherence, displayed d_A
(blueprint: def-sf-integral-basic-realization-data). -/
def basicUnaryTarget (X Y : Scheme.{u}) (A : System l E X ⥤ System l E Y)
    (B : Integral l E X ⥤ Integral l E Y) := (basicUnaryDomain l E X Y A).ι ⋙ B

/-- The proper comparison carries the actual system projections to the defining
proper-image Roos triangle, with exactly its coefficient-restriction transitions.
Source: blueprint proper reduction tower, primitive realization proof Step 3
(blueprint: def-sf-integral-basic-realization-data). -/
def basicProperTower (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : Integral l E X)
    (d : (coefficientSequenceLimit l E Y).obj
      ((Operations.push l E o p).obj ((calculus l E X).reduction.obj K)) ≅
        (ringedPush l E p).obj K) : Prop :=
  (fun [_products : HasCountableProducts (Integral l E Y)] ↦
    ∃ (V : SfIntegralDirectImage l E p K) (e : V.obj ≅ (ringedPush l E p).obj K),
      ∀ n : ℕ,
        d.hom ≫ e.inv ≫ V.projection ≫ Pi.π (sfDirectImageTerm l E p K) n =
          (coefficientSequenceProjection l E Y n).app
              ((Operations.push l E o p).obj ((calculus l E X).reduction.obj K)) ≫
            (scalarReductionDerivedRestriction l E Y n).map
              (((o.evaluation p).evaluation n).hom.app ((calculus l E X).reduction.obj K) ≫
                (proEtaleConstantDerivedDirectImage p
                  (Padic.coefficientExtensionRing l E (n + 1))).map
                    (((calculus l E X).reductionEvaluation n).hom.app K)))
    (_products := integralOperationsDerivedCountableProducts l E Y)

/-- Primitive comparisons and their prescribed maps. The model is normalized on
whole K-flat systems, and its open reduction is the actual open-adjunction mate.
The support conjunct includes an isomorphism in D(strict towers), with all coefficient
transitions, as well as the realized natural isomorphism.
Source: fix-prop-coherence, primitive comparison refinement
(blueprint: def-sf-integral-basic-realization-data). -/
def HasBasicRealizations (D : FiniteFieldDatum.{u}) (o : Operations l E) : Prop :=
  ∃ (model : RealizationModel l E o),
  ∃ (unit : ∀ (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    (K : Integral l E W),
    sfIntegralConstructible l E W K → Good l E W ((calculus l E W).reduction.obj K) →
      IsIso ((calculus l E W).adjunction.unit.app K)),
  ∃ (pull : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v],
    basicUnarySource l E Y X (IntegralSystemRealization.pull l E v) ≅
      basicUnaryTarget l E Y X (IntegralSystemRealization.pull l E v)
        (integralDerivedPullback l E v)),
  ∃ (_pull_spec : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v],
    pull v = Functor.isoWhiskerLeft
      (basicUnaryDomain l E Y X (IntegralSystemRealization.pull l E v)).ι
      (pullbackTensorIntegralPullbackModel l E v).symm),
  ∃ (tensor : ∀ (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))],
    (basicTensorDomain l E W).ι ⋙
        (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
          (calculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W ≅
      (basicTensorDomain l E W).ι ⋙ integralCompletedTensor l E W),
  ∃ (_tensor_spec : ∀ (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))],
    tensor W = Functor.isoWhiskerLeft (basicTensorDomain l E W).ι
      (pullbackTensorIntegralTensorModel l E W).symm),
  ∃ (proper : ∀ {X Y : Scheme.{u}} (p : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [p.IsOver (Spec (.of D.k))] [IsProper p],
    basicUnarySource l E X Y (Operations.push l E o p) ≅
      basicUnaryTarget l E X Y (Operations.push l E o p) (ringedPush l E p)),
  ∃ (_proper_spec : ∀ {X Y : Scheme.{u}} (p : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [p.IsOver (Spec (.of D.k))] [IsProper p]
    (K : (basicUnaryDomain l E X Y (Operations.push l E o p)).FullSubcategory),
    (proper p).hom.app K =
      (model.push l E p).hom.app ((calculus l E X).reduction.obj K.obj) ≫
        (ringedPush l E p).map
          (@inv _ _ _ _ ((calculus l E X).adjunction.unit.app K.obj)
            (unit X K.obj K.property.1 K.property.2.1))),
  ∃ (_properTower : ∀ {X Y : Scheme.{u}} (p : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [p.IsOver (Spec (.of D.k))] [IsProper p]
    (K : (basicUnaryDomain l E X Y (Operations.push l E o p)).FullSubcategory),
    basicProperTower l E o p K.obj ((proper p).app K)),
  ∃ (openUnit : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    (K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory),
    IsIso ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K.obj))),
  ∃ (_openReduction : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    (K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory),
    IsIso ((model.openReduction l E j).app K.obj)),
  ∃ (openComparison : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))],
    basicUnarySource l E X Y (Operations.shriek l E o j) ≅
      basicUnaryTarget l E X Y (Operations.shriek l E o j) (ringedOpen l E j)),
  ∃ (_open_spec : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    (K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory),
    (openComparison j).hom.app K =
      (coefficientSequenceLimit l E Y).map ((model.openReduction l E j).app K.obj) ≫
        @inv _ _ _ _ ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K.obj))
          (openUnit j K)),
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (l : D.k)) (c : Compactification f),
    ∃ (T : Integral l E X ⥤ coefficientSequenceRestrictedDerived l E Y)
      (e : ∀ n : ℕ,
        T ⋙ coefficientConstantTowerEvaluation l E Y n ≅ compactSupportRestrictedLevel l E c n),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2 ∧
      HEq e (Classical.choose (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (exists_compactSupportReductionTower l E D.k X Y f hl c))).2.2).2).2) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (K : (basicSupportDomain l E o c).FullSubcategory),
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
            (T.obj K.obj) ≫ (e n).hom.app K.obj =
          (e m).hom.app K.obj ≫ compactSupportRestrictedTransition l E c m n h K.obj) ∧
      ∃ (tower : (basicSupportDomain l E o c).ι ⋙ (calculus l E X).reduction ⋙
          Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
            coefficientSequenceDerivedRestriction l E Y ≅ (basicSupportDomain l E o c).ι ⋙ T)
        (d : (basicSupportDomain l E o c).ι ⋙ (calculus l E X).reduction ⋙
          Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
            coefficientSequenceLimit l E Y ≅
          basicSupportInput l E o c ⋙ sfCompactSupportFiniteIntegralFunctor l D.k hl c E ⋙
            (sfIntegralConstructible l E Y).ι),
        ∃ hunit : ∀ K : (basicSupportDomain l E o c).FullSubcategory,
          IsIso ((calculus l E c.Z).adjunction.unit.app ((ringedOpen l E c.i).obj K.obj)),
        (∀ K : (basicSupportDomain l E o c).FullSubcategory,
          d.hom.app K =
            (model.push l E c.g).hom.app
              ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj)) ≫
            (ringedPush l E c.g).map
              ((coefficientSequenceLimit l E c.Z).map
                  ((model.openReduction l E c.i).app K.obj) ≫
                @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
                  ((ringedOpen l E c.i).obj K.obj)) (hunit K)) ≫
            (sfQcqsCompactSupportRealization l E D.k hl c).hom.app
              ((basicSupportInput l E o c).obj K)) ∧
        (∀ (K : (basicSupportDomain l E o c).FullSubcategory) (n : ℕ),
          (coefficientConstantTowerEvaluation l E Y n).map (tower.hom.app K) ≫
            (e n).hom.app K.obj =
          (coefficientRestrictedEvaluationIso l E Y n).hom.app
              ((Operations.push l E o c.g).obj
                ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj))) ≫
            (scalarReductionDerivedRestriction l E Y n).map
              ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K.obj) ≫
                (sfAmbientCompactSupportCandidate
                  (Padic.coefficientExtensionRing l E (n + 1)) c).map
                  (((calculus l E X).reductionEvaluation n).hom.app K.obj))) ∧
        (∀ (K : (basicSupportDomain l E o c).FullSubcategory) (n : ℕ),
          (scalarReductionDerivedExtension l E Y n).map (d.hom.app K) ≫
            (sfCompactSupportFiniteReductionIso l D.k hl c E
              ((basicSupportInput l E o c).obj K) n).hom =
          ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
            ((coefficientSequenceProjection l E Y n).app
                ((Operations.push l E o c.g).obj
                  ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K.obj))) ≫
              (scalarReductionDerivedRestriction l E Y n).map
                ((supportEvaluation l E o c n).hom.app ((calculus l E X).reduction.obj K.obj) ≫
                  (sfAmbientCompactSupportCandidate
                    (Padic.coefficientExtensionRing l E (n + 1)) c).map
                    (((calculus l E X).reductionEvaluation n).hom.app K.obj))))

end WeilConjectures.IntegralSystemRealization
