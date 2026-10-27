/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.FinitePullbackTensorConstruction
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CompletedPullbackTowerCore
import Sheaf.Paper.CompletedPullbackTowerNaturality
import all Sheaf.Paper.CoherentTensorRoosComparison
import Sheaf.Paper.NaturalCoherentTensorLevel
import Sheaf.Paper.UnitNormalizedCochainTensor
import Sheaf.Paper.SitePullbackTensorGenerators
import Sheaf.Paper.IntegralPullbackDescentComponents
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.CompletedTowerFinitePullbackKFlat
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Coherent reduction and strict tower realizations

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tower-realizations).

## Main definitions

* `pullbackTensorOrdinaryReduction` and its adjunction fix coherent reduction.
* `pullbackTensorLimitRoos` fixes the total-limit/Roos normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory


section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Each coherent tensor slice is the recorded strict finite total tensor.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorTensorTowerLevel (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)))).obj
            (op n) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P,Q)).obj (op n) :=
  pullbackTensorRestrictedLevel l E W _ n ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    (coefficientEvaluationTensorIso l E W n _ _) ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapIso
        (Iso.prod ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm
          ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm))

/-- The tensor slice comparisons form a strict system map with the actual quotient maps.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: the reduction comparisons preserve scalar-extension units and the evaluation
tensor map sends pure tensors to their two evaluated factors. Across every quotient
transition both routes send x tensor y to its two reduced factors. Tensor generators,
sheafification and total-summand injections give strict equality. The displayed
components therefore define a tower isomorphism and determine it uniquely. -/
theorem pullbackTensorTensorTower_existsUnique (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ∃! e : pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P,Q),
      ∀ n : ℕ, e.app (op n) = pullbackTensorTensorTowerLevel l E W P Q n := by
  sorry

/-- The uniquely prescribed strict tensor tower comparison.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorTensorTower (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  pullbackTensorUniqueChoice (pullbackTensorTensorTower_existsUnique l E W P Q)

private theorem pullbackTensorTensorTower_app (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorTensorTower l E W P Q).app (op n) =
      pullbackTensorTensorTowerLevel l E W P Q n :=
  (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose_spec n

private theorem pullbackTensorTensorLevelComparison_app (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorTensorLevelComparison l E W n).app (P,Q) =
      pullbackTensorTensorTowerLevel l E W P Q n := by
  apply Iso.ext
  rfl

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor
  pullbackTensorTensorLevelComparison pullbackTensorTensorTower pullbackTensorTensorTowerLevel
  integralOperationsTensorLevel in
private theorem pullbackTensorTensorTower_naturality (W : Scheme.{u})
    {P Q : CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ} (g : P ⟶ Q) :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).map
            ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
              ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))).map g))) ≫
      (pullbackTensorTensorTower l E W Q.1 Q.2).hom =
    (pullbackTensorTensorTower l E W P.1 P.2).hom ≫
      (integralOperationsTensorTowerFunctor l E W).map g := by
  apply pullbackTensorTowerNaturality_from_levelComparison l E W
    (fun P Q ↦ pullbackTensorTensorTower l E W P Q) ?_ g
  intro P Q n
  exact (pullbackTensorTensorTower_app l E W P Q n).trans
    (pullbackTensorTensorLevelComparison_app l E W P Q n).symm

/-- The total limit of a coherent complex, normalized by the actual Roos model.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorLimitRoos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos (pullbackTensorRestrictedTower l E W C)) :=
  (coefficientConstantTowerLimit l E W).mapIso
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
  (pullbackTensorRoosModel l E W).app
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

/-- Pullback in the coherent reduction/limit presentation, before restricting objects.
Source: Stacks 0941, 099N (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorReferencePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f ⋙
    coefficientSequenceLimit l E X

/-- Completed tensor in the coherent reduction/limit presentation.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorReferenceTensor (W : Scheme.{u}) :=
  ((pullbackTensorCalculus l E W).reduction.prod
    (pullbackTensorCalculus l E W).reduction) ⋙
      (pullbackTensorCalculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W

/-- The coherent pullback presentation computes the actual strict finite-pullback Roos model.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorReferencePullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (pullbackTensorReferencePullback l E f).obj (DerivedCategory.Q.obj P.obj) ≅
      (integralOperationsPullbackOnGood l E f).obj P :=
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSequenceDerived l E f).mapIso
      ((pullbackTensorReductionModel l E Y).app P)) ≪≫
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≪≫
  pullbackTensorLimitRoos l E X _ ≪≫
  DerivedCategory.Q.mapIso
    (integralOperationsRoosFunctor.mapIso (pullbackTensorPullbackTower l E f P.obj))

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted in
private def pullbackTensorReferencePullbackModelIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ pullbackTensorReferencePullback l E f ≅
      integralOperationsPullbackOnGood l E f := by
  let R := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
  let I := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let S := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let T := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := integralTowerModules l E X) (c := .up ℤ)
  let t : R ⋙ I ⋙ S ⋙ T ≅ integralOperationsPullbackTowerFunctor l E f :=
    NatIso.ofComponents (fun C ↦ pullbackTensorPullbackTower l E f C) (by
      intro C D g
      exact pullbackTensorPullbackTower_naturality l E f g)
  let r := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E X) ≪≫
    Functor.isoWhiskerLeft S (pullbackTensorRoosModel l E X)
  let a := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (pullbackTensorReductionModel l E Y)
      (pullbackTensorSequenceDerived l E f)) (coefficientSequenceLimit l E X)
  let b := Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
    (Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors
        (coefficientSequenceLimit l E X)))
  let c := Functor.isoWhiskerLeft ((integralOperationsGoodComplex l E Y).ι ⋙ R ⋙ I) r
  let d := Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight t integralOperationsRoosFunctor)
      DerivedCategory.Q)
  exact a ≪≫ b ≪≫ c ≪≫ d

private theorem pullbackTensorReferencePullbackModelIso_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (pullbackTensorReferencePullbackModelIso l E f).app P =
      pullbackTensorReferencePullbackModel l E f P := by
  apply Iso.ext
  rfl

attribute [local irreducible] integralPullbackDescent pullbackTensorReferencePullbackModel in
attribute [local implicit_reducible] integralDerivedPullback integralDerivedPullbackComparison
  integralOperationsGoodLocalization in
/-- The actual integral pullback is identified with coherent reduction and limit
by equality with its full strict Roos comparison on every good representative.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: the preceding model is a composition of the adjunction-normalized coherent
reduction comparison, exact pullback factorization, the right-derived Roos model,
and the unit-normalized strict tower isomorphism. Thus its representative functor
is exactly integralOperationsPullbackOnGood. Compare the two descents of that
functor. The localization universal property gives the stated unique isomorphism. -/
theorem pullbackTensorIntegralPullbackModel_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : integralDerivedPullback l E f ≅ pullbackTensorReferencePullback l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj) =
          (integralDerivedPullbackComparison l E f).app P ≪≫
            (pullbackTensorReferencePullbackModel l E f P).symm := by
  obtain ⟨e, he, hu⟩ := normalizedDescentComponents_existsUnique
    (integralOperationsGoodLocalization l E Y) (integralPullbackDescent l E f).functor
    (integralOperationsPullbackOnGood l E f) (integralPullbackDescent l E f).comparison
    (integralPullbackDescent l E f).universal (pullbackTensorReferencePullback l E f)
    (pullbackTensorReferencePullbackModelIso l E f)
  refine ⟨e, ?_, ?_⟩
  · intro P
    rw [← pullbackTensorReferencePullbackModelIso_app l E f P]
    exact he P
  · intro e' h'
    apply hu e'
    intro P
    rw [pullbackTensorReferencePullbackModelIso_app]
    exact h' P

/-- The uniquely Roos-normalized integral pullback realization.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorIntegralPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorIntegralPullbackModel_existsUnique l E f)

/-- Ordinary coherent reduction preserves K-flat representatives.
Source: Stacks 06YY and 0941 (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: finite evaluation of reduction is ordinary scalar extension, which preserves
K-flatness. Evaluation is exact and commutes with the total tensor. Componentwise
exactness of semilinear systems detects the acyclicity of every tensor test. -/
theorem pullbackTensorReductionGood (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W)
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  apply pullbackTensorSequenceKFlat_of_evaluations l E W
  intro n
  exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
    ((pullbackTensorReductionEvaluationComplex l E W n).app P.obj)
    ((coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n)

/-- The recorded system tensor model, at the actual sequence-site universes.
Source: Stacks 06YU (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorSystemModel (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W) (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W) (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) Q) :=
  CoefficientTensorModels.iso.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) (pullbackTensorCalculus l E W).systemClosed
    (pullbackTensorCalculus l E W).systemTensorModel P Q hP hQ

/-- The reference tensor computes the prescribed full strict tensor tower.
Source: Stacks 08TC, 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorReferenceTensorModel (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (pullbackTensorReferenceTensor l E W).obj
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≅
      (integralOperationsTensorOnGood l E W).obj (P,Q) :=
  (coefficientSequenceLimit l E W).mapIso
    ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
      (Iso.prod ((pullbackTensorReductionModel l E W).app P)
        ((pullbackTensorReductionModel l E W).app Q))) ≪≫
  (coefficientSequenceLimit l E W).mapIso
    (pullbackTensorSystemModel l E W _ _
      (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).symm ≪≫
  pullbackTensorLimitRoos l E W _ ≪≫
  DerivedCategory.Q.mapIso
    (integralOperationsRoosFunctor.mapIso (pullbackTensorTensorTower l E W P.obj Q.obj))

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor pullbackTensorCalculus in
private def pullbackTensorTensorTowerComparison (W : Scheme.{u}) :
    (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).prod
      ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ))) ⋙
      (coefficientTotalTensor.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)) ⋙ ((coefficientSequenceRestriction l E
      W).mapHomologicalComplex (.up ℤ)) ⋙ (HomologicalComplex.complexOfFunctorsToFunctorToComplex (T
      := ℕᵒᵖ) (V := integralTowerModules l E W) (c := .up ℤ)) ≅ integralOperationsTensorTowerFunctor
      l E W :=
  NatIso.ofComponents (fun C ↦ pullbackTensorTensorTower l E W C.1 C.2) (by
      intro C D g
      exact pullbackTensorTensorTower_naturality l E W g)

private def pullbackTensorReferenceTensorModelIso (W : Scheme.{u}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ pullbackTensorReferenceTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  pullbackTensorCoherentTensorRoosComparison l E W
    (fun P ↦ pullbackTensorReductionGood l E W P) (pullbackTensorTensorTowerComparison l E W)

attribute [local irreducible] coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor pullbackTensorCalculus in
private theorem pullbackTensorReferenceTensorModelIso_app (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (pullbackTensorReferenceTensorModelIso l E W).app (P,Q) =
      pullbackTensorReferenceTensorModel l E W P Q := by
  change (pullbackTensorCoherentTensorRoosComparison l E W
    (fun P ↦ pullbackTensorReductionGood l E W P)
    (pullbackTensorTensorTowerComparison l E W)).app (P,Q) = _
  rw [pullbackTensorCoherentTensorRoosComparison_app]
  rfl

/-- The full strict tensor-model normalization, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorIntegralTensorNormalization (W : Scheme.{u})
    (e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
          (integralCompletedTensorComparison l E W).app (P,Q) ≪≫
            (pullbackTensorReferenceTensorModel l E W P Q).symm

attribute [local irreducible] pullbackTensorIntegralTensorNormalization

attribute [local irreducible] integralCompletedTensorDescent
  pullbackTensorReferenceTensorModel in
attribute [local implicit_reducible] integralCompletedTensor integralCompletedTensorComparison
  integralOperationsGoodLocalization in
/-- The integral tensor realization is fixed by its complete strict Roos model.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: both functors descend integralOperationsTensorOnGood. The preceding
comparison identifies the whole tower and the Roos differential, not just its
finite projections. The localization universal property gives a unique natural
isomorphism compatible with these specified comparison components. -/
theorem pullbackTensorIntegralTensorModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W,
      pullbackTensorIntegralTensorNormalization l E W e := by
  obtain ⟨e, he, hu⟩ := normalizedDescentComponents_existsUnique
    ((integralOperationsGoodLocalization l E W).prod (integralOperationsGoodLocalization l E W))
    (integralCompletedTensorDescent l E W).functor (integralOperationsTensorOnGood l E W)
    (integralCompletedTensorDescent l E W).comparison
    (integralCompletedTensorDescent l E W).universal (pullbackTensorReferenceTensor l E W)
    (pullbackTensorReferenceTensorModelIso l E W)
  refine ⟨e, ?_, ?_⟩
  · unfold pullbackTensorIntegralTensorNormalization
    intro P Q
    rw [← pullbackTensorReferenceTensorModelIso_app l E W P Q]
    exact he (P,Q)
  · intro e' h'
    unfold pullbackTensorIntegralTensorNormalization at h'
    apply hu e'
    rintro ⟨P,Q⟩
    rw [pullbackTensorReferenceTensorModelIso_app]
    exact h' P Q

/-- The uniquely Roos-normalized tensor realization.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorIntegralTensorModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorIntegralTensorModel_existsUnique l E W)

/-- The ordinary tensor comparison on coherent complexes is determined on every
pure-tensor total summand by the actual inverse-image adjunction unit.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: use the ordinary ringed-topos pullback/tensor comparison on each pair of
terms. Its pure-tensor formula is the displayed unit equation. Totalization
respects both differential summands. Tensor generators and total-summand
injections prove uniqueness; the ordinary inverse gives invertibility. -/
theorem pullbackTensorSequenceCochain_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) ⋙
        (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ≅
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).prod
        ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X),
      ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : ℕ × Y.ProEt)
        (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
        ((e.hom.app (P,Q)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj V))
          (((pullbackTensorSequenceAdjunction l E f).unit.app
            (((coefficientTotalTensor.{u, u + 1, u}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app (op V)
            (coefficientTensorGenerator.{u, u + 1, u}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y) P Q p q k h (op V) x y)) =
        coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h (op ((pullbackTensorSequenceBase f).obj V))
          (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X p)).val.app (op V) x)
          (((pullbackTensorSequenceAdjunction l E f).unit.app (Q.X q)).val.app (op V) y) := by
  letI : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  letI : RepresentablyFlat (pullbackTensorSequenceBase f) := by
    refine ⟨fun W ↦ ?_⟩
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence W.1 W.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  exact SemilinearSections.unitNormalizedCochainTensor.{u + 1, u, u}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceTopology (ProEt.topology X)) (pullbackTensorSequenceBase f)
    (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorSequenceRing l E f) (pullbackTensorSequenceInverse l E f)
    (pullbackTensorSequenceAdjunction l E f)
    (SemilinearSections.sitePullbackTensorGenerators
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) (pullbackTensorSequenceBase f)
      (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
      (pullbackTensorSequenceRing l E f) (pullbackTensorSequenceInverse l E f)
      (pullbackTensorSequenceAdjunction l E f)).exists.choose

/-- The pure-tensor normalized comparison of strict coherent complexes.
Source: Stacks 07A4 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorSequenceCochain {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceCochain_existsUnique l E f)

/-- Exact sequence inverse image preserves K-flatness.
Source: Stacks 0DEN, 0DEP and 07A4
(blueprint: lem-pur-sequence-pullback-kflat).
Proof: evaluate at every finite level. Algebraic inverse image preserves arbitrary
K-flat complexes by the conservative stalk criterion; scalar extension preserves
K-flatness. Uniqueness of left adjoints identifies this with the actual finite
pullback. Its specified evaluation comparison and componentwise tensor exactness
then prove K-flatness on the sequence site. No flat-term assumption is used. -/
theorem pullbackTensorSequenceGood {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × X.ProEt) (inferInstance : Category.{u} (ℕ × X.ProEt))
      (pullbackTensorSequenceSmall X) (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply pullbackTensorSequenceKFlat_of_evaluations l E X
  intro n
  exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E X n)
    ((pullbackTensorInverseEvaluationComplex l E f n).app P)
    (completedTowerFinitePullbackKFlat l E f n
      (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
      ((coefficientTensorModelPreservation l E Y).2 P hP n))

/-- The derived coherent comparison is uniquely fixed before applying Rlim.
Source: Stacks 06YU, 07A4 and 0941 (blueprint: def-pur-completed-pullback-tower-realizations).
Proof: restrict the pure-tensor cochain comparison to K-flat pairs. Exact inverse
image preserves these pairs. The displayed square is the localization descent
square with the prescribed tensor and pullback models. The K-flat resolving
localization gives existence and uniqueness, including all system transitions. -/
theorem pullbackTensorSystemComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor,
      ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
        (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
          (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) P)
        (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
          (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) Q),
        (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
              ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
        (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P,Q)) ≫
          (pullbackTensorSystemModel l E X _ _
            (pullbackTensorSequenceGood l E f P hP)
            (pullbackTensorSequenceGood l E f Q hQ)).hom := by
  let JY := coefficientSequenceTopology (ProEt.topology Y)
  let JX := coefficientSequenceTopology (ProEt.topology X)
  let AY := coefficientSequenceCommRingSheaf l E Y
  let AX := coefficientSequenceCommRingSheaf l E X
  let PY : ObjectProperty (CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) _ (pullbackTensorSequenceSmall Y) JY AY
  let PX : ObjectProperty (CochainComplex (coefficientSequenceModules l E X) ℤ) :=
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × X.ProEt) _ (pullbackTensorSequenceSmall X) JX AX
  let V := (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ)).inverseImage
    PY.ι
  letI : (PY.ι ⋙ DerivedCategory.Q).IsLocalization V :=
    CategoryTheory.RingedDerivedNative.kFlatLocalization.{u + 1, u, u} JY AY
  let ff' := Localization.fullyFaithfulWhiskeringLeft
    ((PY.ι ⋙ DerivedCategory.Q).prod (PY.ι ⋙ DerivedCategory.Q)) (V.prod V)
    (DerivedCategory (coefficientSequenceModules l E X))
  exact tensorComparisonDescent DerivedCategory.Q DerivedCategory.Q
    ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ))
    (pullbackTensorSequenceDerived l E f)
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom PY PX
    (fun P hP ↦ pullbackTensorSequenceGood l E f P hP) ff'
    (coefficientTotalTensor.{u, u + 1, u} JY AY)
    (coefficientTotalTensor.{u, u + 1, u} JX AX)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorCalculus l E Y).systemTensorModel.comparison
    (pullbackTensorCalculus l E X).systemTensorModel.comparison
    (pullbackTensorSequenceCochain l E f)
    (fun P _ ↦ ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app P).isIso_hom)
    (fun P Q _ _ ↦ ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app
      ((coefficientTotalTensor.{u, u + 1, u} JY AY).obj (P,Q))).isIso_hom)

/-- The canonical comparison as a map of coherent derived systems.
Source: Stacks 07A4 and 0941 (blueprint: def-pur-completed-pullback-tower-realizations). -/
def pullbackTensorSystemComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorSystemComparison_existsUnique l E f)

end CoherentSystems

end WeilConjectures
