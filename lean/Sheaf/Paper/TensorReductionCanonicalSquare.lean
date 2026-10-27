/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompletedPullbackTowerRealizations
public import Sheaf.Paper.TensorReductionStrictComparison

/-! # Canonical representative square for coherent reduction tensor

Source: Stacks 07A4, 07A6 and 0941.
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
attribute [local irreducible] pullbackTensorReductionModel pullbackTensorSystemModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite-component predicate used to identify the strict assembled map. -/
def tensorReductionFiniteProperty (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (ψ : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ⟶
      (coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P,
          ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)) : Prop :=
  ∀ n : ℕ,
    ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map ψ =
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E W P Q)

/-- The normalized reduction tensor square admits a representative map before
selecting the uniquely assembled strict map.

Source: Stacks 07A4 and 07A6; transport of the simultaneous representative normalization.
(blueprint: lem-coef-tensor-reduction-strict-derived-square). -/
theorem tensorReductionCanonicalSquare_exists (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hT : integralOperationsGoodComplex l E W
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj))) :
    let S := pullbackTensorCalculus l E W
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P.obj, G.obj Q.obj)
    ∃ ψ : G.obj T ⟶ B,
      S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
          P.obj Q.obj P.property.1 Q.property.1).hom) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        S.systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
            ((pullbackTensorReductionModel l E W).hom.app Q)) =
      (pullbackTensorReductionModel l E W).hom.app ⟨T, hT⟩ ≫
        DerivedCategory.Q.map ψ ≫
        (pullbackTensorSystemModel l E W _ _
          (pullbackTensorReductionGood l E W P)
          (pullbackTensorReductionGood l E W Q)).hom ∧
      tensorReductionFiniteProperty l E W P.obj Q.obj ψ := by
  sorry

end WeilConjectures
