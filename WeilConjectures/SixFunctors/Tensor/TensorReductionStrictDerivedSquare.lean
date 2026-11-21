/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SixFunctors.Tensor.TensorReductionCanonicalSquare

/-! # Derived normalization of the strict reduction tensor map

## References

* [Stacks, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
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

/-- The strict balanced map satisfies the representative square for derived reduction.
The ordinary map is already constructed and characterized by its finite components.
This assertion only identifies its localization with the recorded tensor comparison. -/
theorem tensorReductionStrictMap_derived_square (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (hT : integralOperationsGoodComplex l E W
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj))) :
    let S := pullbackTensorCalculus l E W
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
    S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
        P.obj Q.obj P.property.1 Q.property.1).hom) ≫
      S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      S.systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
          ((pullbackTensorReductionModel l E W).hom.app Q)) =
    (pullbackTensorReductionModel l E W).hom.app ⟨T, hT⟩ ≫
      DerivedCategory.Q.map (tensorReductionStrictMap l E W P.obj Q.obj) ≫
      (pullbackTensorSystemModel l E W _ _
        (pullbackTensorReductionGood l E W P)
        (pullbackTensorReductionGood l E W Q)).hom := by
  dsimp only
  obtain ⟨ψ, hψ, hψcomp⟩ := tensorReductionCanonicalSquare_exists l E W P Q hT
  have huniq := tensorReductionStrictMap_existsUnique l E W P.obj Q.obj
  dsimp only at huniq
  have hψprop : ∀ n : ℕ,
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map ψ =
        tensorReductionSystemFiniteComponent l E W P.obj Q.obj n := by
    intro n
    unfold tensorReductionFiniteProperty at hψcomp
    exact (hψcomp n).trans (huniq.choose_spec.1 n)
  have hψeq : ψ = tensorReductionStrictMap l E W P.obj Q.obj := by
    apply huniq.unique hψprop
    exact huniq.choose_spec.1
  simpa only [hψeq] using hψ

end WeilConjectures
