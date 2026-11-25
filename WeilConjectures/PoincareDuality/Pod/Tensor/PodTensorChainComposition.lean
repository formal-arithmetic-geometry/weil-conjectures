/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorReindexChain
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRawComposition

/-! # The tensor Roos chain composition equation

We state the composition equation for the explicit tensor Roos chain maps of a reindexing
family, before localization (`PodTensorChainComposition`).

## Implementation details

Both sides use the explicitly constructed chain maps from the tensor tower data; the equation
involves neither a derived tensor comparison nor constructibility.

## References

* [Stacks, Tags 07A4, 0941]
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
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The composition equation for the explicit tensor Roos chain maps before localization: for
isomorphisms `h : Z ⟶ W` and `f : W ⟶ V`, the chain maps of `f` and `h` compose to that of
`h ≫ f` on the good representatives `P`, `Q`, through the composition isomorphism of the
reindexing family `A`. -/
def PodTensorChainComposition
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory) : Prop :=
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    let FP := (podGoodReindex l E f (A.completion f)).obj P
    let FQ := (podGoodReindex l E f (A.completion f)).obj Q
    PodRoosCompositionEquation (isoReductionIntegralComplex l E h)
      integralOperationsRoosFunctor
      (α.hom.app (integralOperationsRoosFunctor.obj
        ((integralOperationsTensorTowerFunctor l E V).obj (P.obj, Q.obj))))
      (podTensorReindexChain l E f (A.completion f) (A.tensor f) P Q)
      (podTensorReindexChain l E h (A.completion h) (A.tensor h) FP FQ)
      (podTensorReindexChain l E (h ≫ f) (A.completion (h ≫ f))
        (A.tensor (h ≫ f)) P Q)
      ((integralOperationsTensorTowerFunctor l E Z).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj)))

end WeilConjectures
