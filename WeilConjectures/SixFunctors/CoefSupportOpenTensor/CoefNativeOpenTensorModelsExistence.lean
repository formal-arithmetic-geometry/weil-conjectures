/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorGammaEvaluation
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorModelsDataExistence

/-! # Native normalized open tensor models and evaluation

We show that native open tensor models exist at the sequence and finite levels, and that the
prescribed finite evaluation comparisons identify their gamma transformations.

## Implementation details

The restriction tensor comparison on ordinary module sheaves sends `x ⊗ y` to the tensor of the
restrictions; the inverse open comparison is the adjoint transpose of the open unit followed by
the inverse restriction comparison, an isomorphism by [Stacks, Tag 0E8I]. Its summands are
totalized using coproduct preservation by open extension, and K-flat resolutions identify the
total tensor with the prescribed derived tensors. The same construction is done over each finite
coefficient ring; exact evaluation preserves all ingredients, so both sides of `GammaEvaluation`
are the same chain map on homogeneous generators. No flatness of a quotient map or boundedness
is required.

## References

* [Stacks, Tag 0E8I]
* [Stacks, Tag 0GL1]
* [Stacks, Tag 07A4]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Native open tensor models exist at the sequence and finite levels, and the
prescribed finite evaluation comparisons identify their gamma transformations. -/
theorem nativeOpenTensorModels_exists {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z) :
    ∃ (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors)
      (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n),
      GammaEvaluation l E j SX SZ O On := by
  obtain ⟨O, On, _⟩ := nativeOpenTensorModels_data_exists l E j SX SZ
  exact ⟨O, On, nativeOpenTensorGammaEvaluation l E j SX SZ O On⟩

end WeilConjectures.CoefSupportOpenTensor
