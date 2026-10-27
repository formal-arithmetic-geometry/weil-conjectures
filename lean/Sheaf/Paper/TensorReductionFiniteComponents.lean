/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.CompletedPullbackTowerCore
public import Sheaf.Paper.TensorReductionEvaluationIdentification

/-! # Finite components of ordinary reduction tensor comparison

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] pullbackTensorReductionEvaluationComplex
  coefficientScalarTensorIso coefficientEvaluationTensorIso
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The balanced finite scalar tensor map, transported to ordinary reductions.
Source: Stacks 07A4 (blueprint: lem-coef-tensor-reduction-finite-components). -/
def tensorReductionFiniteComponent (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj (G.obj T) ⟶
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj B :=
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
    (coefficientScalarTensorIso l E W n P Q).hom ≫
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
      (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).hom.app P)
        ((pullbackTensorReductionEvaluationComplex l E W n).hom.app Q)) ≫
    (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).inv

/-- The same component using literal vertical evaluation of the sequence ring.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-finite-components). -/
def tensorReductionSystemFiniteComponent (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).obj
          (G.obj T) ⟶
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).obj B :=
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
  let e := tensorReductionEvaluationComplexIso l E W n
  e.inv.app (G.obj T) ≫ tensorReductionFiniteComponent l E W P Q n ≫ e.hom.app B

/-- The balanced finite tensor maps commute with every quotient transition,
before localization, without K-flatness or flat-term hypotheses.

Source: Stacks 07A4 and 0941; step 1 of
lem-coef-tensor-reduction-ordinary-model.
Proof: use the ordinary reduction/evaluation adjunction-unit equations to replace
both finite reductions by scalar extension. Transpose through the scalar
adjunction at level n. On the total summand of bidegree (p,q), both routes send
b tensor (x tensor y) to the tensor of the two quotient reductions, multiplying
b into the first factor. Scalar balancing gives equality for all b. The ordinary
scalar and evaluation tensor comparisons have exactly these generator formulas.
Sheafification and the total-summand universal properties give equality in each
degree. The formula uses the actual quotient maps, hence works also for m = n;
zero complexes and the empty site give the same equality of zero maps.
(blueprint: lem-coef-tensor-reduction-finite-components). -/
theorem tensorReductionFiniteComponents_compatible (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ∀ (i : ℤ) {m n : ℕ} (h : m ≤ n),
      (tensorReductionSystemFiniteComponent l E W P Q n).f i ≫
          SheafOfModules.sequenceSystemTransition
            (coefficientSequenceCommRingSystem l E W) (B.X i) h =
        SheafOfModules.sequenceSystemTransition
            (coefficientSequenceCommRingSystem l E W) ((G.obj T).X i) h ≫
          (SheafOfModules.systemRestriction (coefficientSequenceCommRingSystem l E W) h).map
            ((tensorReductionSystemFiniteComponent l E W P Q m).f i) := by sorry

end WeilConjectures
