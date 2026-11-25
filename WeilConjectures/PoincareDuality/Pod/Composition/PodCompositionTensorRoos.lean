/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorChainComposition
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionTensorTower
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorChainCompositionProof

/-! # Composition of normalized strict tensor Roos maps

We show that the strict tensor Roos maps are compatible with composition of reindexings along
isomorphisms, before localization (`podCompositionTensorRoos`).

## Implementation details

The strict tensor-tower square is checked on pure tensors in each quotient and homogeneous
summand. For the Roos realization, the two coordinates of the mapping cocone are compared using
the `RoosFst` and `RoosSnd` formulas; they are jointly monic.

## References

* Stacks Project, Tags 07A4, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex
  integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralOperationsRoos
attribute [local implicit_reducible] integralOperationsRoosFunctor

-- The three coefficient actions and their whole-tower comparisons elaborate together.
/-- Composition before localization of the strict tensor Roos maps.
For isomorphisms `h : Z ⟶ W` and `f : W ⟶ V`, the strict tensor Roos maps of `f`, `h` and
`h ≫ f` satisfy the composition equation `PodTensorChainComposition`, as chain maps. -/
theorem podCompositionTensorRoos
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (hf : PodCompletionReindex.Laws l E f (A.completion f))
    (hh : PodCompletionReindex.Laws l E h (A.completion h))
    (hhf : PodCompletionReindex.Laws l E (h ≫ f) (A.completion (h ≫ f)))
    (htf : PodCompletedTensorReindex.Generators l E f (A.completion f) (A.tensor f))
    (hth : PodCompletedTensorReindex.Generators l E h (A.completion h) (A.tensor h))
    (hthf : PodCompletedTensorReindex.Generators l E (h ≫ f)
      (A.completion (h ≫ f)) (A.tensor (h ≫ f)))
    (ha : ∀ (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory) :
    PodTensorChainComposition l E A h f P Q := by
  exact podTensorChainComposition l E A h f hf hh hhf P Q
    (podCompositionTensorTower l E A h f
      hf.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hhf.2.2.2.2.2.2.1 htf hth hthf ha P Q)

end WeilConjectures
