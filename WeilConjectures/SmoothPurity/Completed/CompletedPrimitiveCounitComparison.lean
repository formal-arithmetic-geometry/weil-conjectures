/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
public import WeilConjectures.SmoothPurity.PrimitiveCounit.PrimitiveCounitEvaluation
public import WeilConjectures.SixFunctors.PrimitiveCounit.PrimitiveCounitComparisonModels
import WeilConjectures.SmoothPurity.Supporting.PrimitiveCounitTensorRealization
import WeilConjectures.SmoothPurity.Supporting.PrimitiveCounitPullbackRealization
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosNormalization

/-! # Quotient-limit realization and primitive coherent-counit comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
with the strict Roos normalization and the coherent coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Natural number n means positive coefficient exponent n+1. All systems are derived
before evaluation, and the site has independent object and morphism universes t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace PrimitiveCounit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Padic
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] Scheme.coefficientProEtaleDirectRingMap
attribute [local irreducible] WeilConjectures.coefficientSequenceCommRingSheaf
attribute [local irreducible] WeilConjectures.coefficientSequenceCommRingPresheaf
attribute [local irreducible] integralCompletedTensor
attribute [local irreducible] integralCompletedTensorComparison
attribute [local irreducible] integralDerivedPullback
attribute [local irreducible] integralDerivedPullbackComparison
attribute [local irreducible] Functor.leftAdjoint
attribute [local irreducible] inverseEvaluation
attribute [local irreducible] inverse
attribute [local irreducible] direct
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] roosF
attribute [local irreducible] roosEval
attribute [local irreducible] roosι
attribute [local irreducible] limitComplexIso
attribute [local irreducible] Functor.rightDerivedFunctorObjQIso
attribute [local implicit_reducible] SheafOfModules.instAbelian
attribute [local implicit_reducible] abelianOfAdjunction
attribute [local implicit_reducible] Abelian.ofCoimageImageComparisonIsIso
attribute [local implicit_reducible] scalarReductionSourceDerived
attribute [local implicit_reducible] scalarReductionTargetDerived
attribute [local implicit_reducible] coefficientConstantTowerDerived
attribute [local implicit_reducible] integralOperationsCommHasDerivedCategory
attribute [local implicit_reducible] integralTowerHasDerivedCategory
attribute [local implicit_reducible] integralCompletedRingHasDerivedCategory
attribute [local instance 5000] scalarReductionSourceDerived
attribute [local instance 5000] coefficientConstantTowerDerived
attribute [local irreducible] coefficientConstantTowerProjection
attribute [local irreducible] Functor.rightDerivedFunctor
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] scalarReductionExistence
attribute [local irreducible] scalarReductionDerivedExistence
attribute [local irreducible] unrestrictedIntegralReductionExistence
attribute [local irreducible] RoosResolution
attribute [local irreducible] RoosProjection
attribute [local irreducible] integralOperationsTensorLevel
attribute [local irreducible] coefficientTotalTensor
attribute [local irreducible] integralOperationsRoosFunctor
attribute [local irreducible] finiteTensorBridge
attribute [local irreducible] restrictEvaluation
attribute [local irreducible] inverseComplexEvaluation
attribute [local irreducible] tensorRestrictionIso
attribute [local irreducible] pullRestrictionIso
attribute [local irreducible] roosBridge
attribute [local irreducible] TensorModel
attribute [local irreducible] PullModel
attribute [local irreducible] tensorBeta
attribute [local irreducible] pullBeta
attribute [local instance 5000] SemilinearSections.hasDerived
attribute [local instance 5000] scalarReductionTargetDerived

/-- Natural primitive comparisons, their strict representative normalizations and
inverse words, together with whole-system counit and actual projection naturality.
Source: Stacks 0941, proof steps 1--6 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
structure Comparisons {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y)
    (ρW : RoosRealization l E W) (ρX : RoosRealization l E X) where
  tensor : integralCompletedTensor l E W ≅
    S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W
  geometric : integralDerivedPullback l E f ≅
    V.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X
  tensor_model : TensorModel l E W S ρW tensor
  geometric_model : PullModel l E f V ρX geometric
  geometric_evaluation : ∀ n : ℕ,
    Nonempty (pull l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory)
  counit_effective : ∀ A : coefficientSequenceDerived l E W,
    IsNormalizedCoefficientSequence l E W A → IsIso (S.adjunction.counit.app A)
  geometric_counit_effective : ∀ C : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y C → IsIso (V.adjunction.counit.app C)
  tensor_iso : ∀ A N : coefficientSequenceDerived l E W,
    IsNormalizedCoefficientSequence l E W A → IsNormalizedCoefficientSequence l E W N →
      IsIso (tensorBeta l E W S tensor A N)
  geometric_iso : ∀ C : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y C → IsIso (pullBeta l E f V geometric C)
  tensor_inverse : ∀ (A N : coefficientSequenceDerived l E W)
    (_hA : IsNormalizedCoefficientSequence l E W A)
    (_hN : IsNormalizedCoefficientSequence l E W N)
    (eA : S.reduction.obj ((coefficientSequenceLimit l E W).obj A) ≅ A)
    (eN : S.reduction.obj ((coefficientSequenceLimit l E W).obj N) ≅ N)
    (_heA : eA.hom = S.adjunction.counit.app A)
    (_heN : eN.hom = S.adjunction.counit.app N),
    ∃ b : (integralCompletedTensor l E W).obj
        ((coefficientSequenceLimit l E W).obj A, (coefficientSequenceLimit l E W).obj N) ≅
        (coefficientSequenceLimit l E W).obj (S.systemClosed.tensor.obj (A, N)),
      b.hom = tensorBeta l E W S tensor A N ∧
      b.inv = (coefficientSequenceLimit l E W).map
        (S.systemClosed.tensor.map (Prod.mkHom eA.inv eN.inv)) ≫
          tensor.inv.app ((coefficientSequenceLimit l E W).obj A,
            (coefficientSequenceLimit l E W).obj N)
  geometric_inverse : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C)
    (eC : V.reduction.obj ((coefficientSequenceLimit l E Y).obj C) ≅ C)
    (_heC : eC.hom = V.adjunction.counit.app C),
    ∃ b : (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E Y).obj C) ≅
      (coefficientSequenceLimit l E X).obj ((pull l E f).obj C),
      b.hom = pullBeta l E f V geometric C ∧
      b.inv = (coefficientSequenceLimit l E X).map ((pull l E f).map eC.inv) ≫
        geometric.inv.app ((coefficientSequenceLimit l E Y).obj C)
  tensor_naturality : ∀ {A A' N N' : coefficientSequenceDerived l E W}
    (a : A ⟶ A') (b : N ⟶ N'),
    (integralCompletedTensor l E W).map
        (Prod.mkHom ((coefficientSequenceLimit l E W).map a)
          ((coefficientSequenceLimit l E W).map b)) ≫ tensorBeta l E W S tensor A' N' =
      tensorBeta l E W S tensor A N ≫
        (coefficientSequenceLimit l E W).map (S.systemClosed.tensor.map (Prod.mkHom a b))
  geometric_naturality : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C'),
    (integralDerivedPullback l E f).map ((coefficientSequenceLimit l E Y).map a) ≫
        pullBeta l E f V geometric C' =
      pullBeta l E f V geometric C ≫
        (coefficientSequenceLimit l E X).map ((pull l E f).map a)
  counit_naturality : ∀ {A A' : coefficientSequenceDerived l E W} (a : A ⟶ A'),
    S.reduction.map ((coefficientSequenceLimit l E W).map a) ≫ S.adjunction.counit.app A' =
      S.adjunction.counit.app A ≫ a
  geometric_counit_naturality : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C'),
    V.reduction.map ((coefficientSequenceLimit l E Y).map a) ≫ V.adjunction.counit.app C' =
      V.adjunction.counit.app C ≫ a
  projections : ∀ {A A' : coefficientSequenceDerived l E W} (a : A ⟶ A') (n : ℕ),
    (coefficientSequenceLimit l E W).map a ≫ (coefficientSequenceProjection l E W n).app A' =
      (coefficientSequenceProjection l E W n).app A ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceDerivedEvaluation l E W n).map a)
  geometric_projections : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C') (n : ℕ),
    (coefficientSequenceLimit l E Y).map a ≫ (coefficientSequenceProjection l E Y n).app C' =
      (coefficientSequenceProjection l E Y n).app C ≫
        (coefficientFiniteDerivedRestriction l E Y n).map
          ((coefficientSequenceDerivedEvaluation l E Y n).map a)

end PrimitiveCounit

section RoosExistenceProof

/-- Retain the derived-limit unit equation while constructing both Roos normalizations.
Source: Stacks Tag 0941 and the proved normalizedRoosIso construction. -/
private theorem primitiveRoosRealization_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t}) :
    Nonempty (PrimitiveCounit.RoosRealization l E W) := by
  exact coefficientConstantTowerRoosNormalization l E W

end RoosExistenceProof

set_option linter.unusedVariables false in
/-- The normalized Roos realizations required by the completed comparison exist.
Source: Stacks 0941 and the strict Roos comparison; choose the common quotient
tower and its projection/resolution normalization.
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
theorem completedPrimitiveCounit_roos_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y) :
    Nonempty (PrimitiveCounit.RoosRealization l E W ×
      PrimitiveCounit.RoosRealization l E X) := by
  obtain ⟨ρW⟩ := primitiveRoosRealization_exists l E W
  obtain ⟨ρX⟩ := primitiveRoosRealization_exists l E X
  exact ⟨ρW, ρX⟩

section ComparisonAssembly
attribute [local irreducible] coefficientSequenceLimit

/-- Counit invertibility is independent of the presentation of the left adjoint.
Source: normalized reconstruction and Mathlib Adjunction.leftAdjointUniq_hom_app_counit.
(blueprint: lem-pur-completed-primitive-counit-comparisons-existence).
Proof: choose the full evaluation calculus, whose counit is invertible on normalized
systems. The left-adjoint comparison for the common total-limit right adjoint
expresses the given counit as this counit after an isomorphism. -/
private theorem primitiveCounitEffective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (S : CoefficientDerivedSystemReduction l E W)
    (A : coefficientSequenceDerived l E W)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsIso (S.adjunction.counit.app A) := by
  obtain ⟨T, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  have : IsIso (T.adjunction.counit.app A) :=
    ((purNormalizedReconstructionOfScheme l E W T).1 A hA).2
  rw [← S.adjunction.leftAdjointUniq_hom_app_counit T.adjunction A]
  infer_instance

/-- The normalized tensor and geometric models assemble into the comparison record
for any already chosen Roos realizations. Source: Stacks 0941; the counit
calculation and projection naturality are the remaining assembly steps.
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
theorem completedPrimitiveCounit_comparisons_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y)
    (ρW : PrimitiveCounit.RoosRealization l E W)
    (ρX : PrimitiveCounit.RoosRealization l E X) :
    Nonempty (PrimitiveCounit.Comparisons l E f W S V ρW ρX) := by
  classical
  obtain ⟨tensor, hTensor⟩ := primitiveCounitTensorRealization l E W S ρW
  obtain ⟨geometric, hGeometric⟩ := primitiveCounitPullbackRealization l E f V ρX
  have hW := primitiveCounitEffective l E W S
  have hY := primitiveCounitEffective l E Y V
  refine ⟨{
    tensor := tensor
    geometric := geometric
    tensor_model := hTensor
    geometric_model := hGeometric
    geometric_evaluation := ?_
    counit_effective := hW
    geometric_counit_effective := hY
    tensor_iso := ?_
    geometric_iso := ?_
    tensor_inverse := ?_
    geometric_inverse := ?_
    tensor_naturality := ?_
    geometric_naturality := ?_
    counit_naturality := fun a ↦ S.adjunction.counit.naturality a
    geometric_counit_naturality := fun a ↦ V.adjunction.counit.naturality a
    projections := fun a n ↦ (coefficientSequenceProjection l E W n).naturality a
    geometric_projections := fun a n ↦ (coefficientSequenceProjection l E Y n).naturality a
  }⟩
  · intro n
    have : (integralOperationsLevelPullback l E f n).Additive :=
      integralOperationsLevelPullback_additive l E f n
    have : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
      PrimitiveCounit.levelLimits l E f n
    have : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
      PrimitiveCounit.levelColimits l E f n
    unfold PrimitiveCounit.pull coefficientSequenceDerivedEvaluation
    exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (PrimitiveCounit.inverseEvaluation l E f n) ≪≫
        Functor.mapDerivedCategoryCompIso _ _⟩
  · intro A N hA hN
    have := hW A hA
    have := hW N hN
    have : IsIso (Prod.mkHom (S.adjunction.counit.app A)
        (S.adjunction.counit.app N)) :=
      (isIso_prod_iff (f := Prod.mkHom (S.adjunction.counit.app A)
        (S.adjunction.counit.app N))).2 ⟨inferInstance, inferInstance⟩
    unfold PrimitiveCounit.tensorBeta
    infer_instance
  · intro C hC
    have := hY C hC
    unfold PrimitiveCounit.pullBeta
    infer_instance
  · intro A N _ _ eA eN heA heN
    let b := tensor.app ((coefficientSequenceLimit l E W).obj A,
      (coefficientSequenceLimit l E W).obj N) ≪≫
      (coefficientSequenceLimit l E W).mapIso
        (S.systemClosed.tensor.mapIso (eA.prod eN))
    refine ⟨b, ?_, ?_⟩
    · simp only [b, PrimitiveCounit.tensorBeta, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Iso.prod_hom, heA, heN]
    · rfl
  · intro C _ eC heC
    let b := geometric.app ((coefficientSequenceLimit l E Y).obj C) ≪≫
      (coefficientSequenceLimit l E X).mapIso ((PrimitiveCounit.pull l E f).mapIso eC)
    refine ⟨b, ?_, ?_⟩
    · simp only [b, PrimitiveCounit.pullBeta, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, heC]
    · rfl
  · intro A A' N N' a b
    let β : (coefficientSequenceLimit l E W).prod (coefficientSequenceLimit l E W) ⋙
        integralCompletedTensor l E W ⟶
        S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W :=
      Functor.whiskerLeft ((coefficientSequenceLimit l E W).prod (coefficientSequenceLimit l E W))
          tensor.hom ≫
        Functor.whiskerRight (S.adjunction.counit.prod S.adjunction.counit)
          (S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W)
    unfold PrimitiveCounit.tensorBeta
    exact β.naturality (Prod.mkHom a b)
  · intro C C' a
    let β : coefficientSequenceLimit l E Y ⋙ integralDerivedPullback l E f ⟶
        PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X :=
      Functor.whiskerLeft (coefficientSequenceLimit l E Y) geometric.hom ≫
        Functor.whiskerRight V.adjunction.counit
          (PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X)
    unfold PrimitiveCounit.pullBeta
    exact β.naturality a

end ComparisonAssembly

/-- Quotient-limit realization of completed tensor and pullback, with primitive
comparisons given by the coherent system counit. The calculus parameters provide
the dependency's canonical reduction and its tensor models, with no arbitrary maps.
Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
refined by lem-weil-strict-roos-comparison and the coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Proof, following every step of the node:
1. Choose flat-term K-flat representatives P,Q by lem-pc-kflat-resolution. Their
quotients are K-flat by lem-pur-kflat-change-of-rings. Componentwise exactness gives
K-flatness as whole systems. Their tensor and inverse image are the actual strict
quotient tensor and pullback towers, with the prescribed transitions on generators.
2. Restrict to completed-coefficient towers. Countable products are exact by
lem-weil-proetale-countable-products-exact. Apply lem-weil-strict-roos-comparison:
on a K-injective tower resolution q the map is C(q) followed by the inverse of
the inclusion lim I to C(I) with zero shifted coordinate. It preserves projections.
3. Compose with the representative comparisons of lem-pur-integral-operations-well-defined.
Naturality on strict maps and inversion of quasi-isomorphisms descend to natural
functor isomorphisms. Unique-compatible descent makes them resolution independent.
4. The evaluation-calculus adjunction supplies one whole-system counit. Effectivity
makes its finite evaluations invertible on normalized systems; joint conservativity
makes the whole counit invertible. Its naturality holds for all whole-system maps.
5. Apply tensor or inverse image to these counit isomorphisms, then total limit,
and precompose with realization. Functoriality cancels each counit with its inverse
in both orders, giving exactly the displayed inverse formulas.
6. Apply tensor or inverse image to the whole-system counit naturality equation,
then limit and realization naturality. Actual limit projections are natural on
resolutions, and Roos preserves their equations. Their scalar-extension adjoints
are the evaluated counits by the evaluation calculus. No equality of derived maps
is inferred just from their evaluations. Zero objects, empty schemes and identity
morphisms are included; n=0 denotes exponent one throughout. -/
theorem completedPrimitiveCounitComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y) :
    ∃ (ρW : PrimitiveCounit.RoosRealization l E W)
      (ρX : PrimitiveCounit.RoosRealization l E X),
      Nonempty (PrimitiveCounit.Comparisons l E f W S V ρW ρX) := by
  obtain ⟨⟨ρW, ρX⟩⟩ := completedPrimitiveCounit_roos_exists
    l E f W _hX _hY _hW S V
  exact ⟨ρW, ρX, completedPrimitiveCounit_comparisons_exists
    l E f W _hX _hY _hW S V ρW ρX⟩

end WeilConjectures
