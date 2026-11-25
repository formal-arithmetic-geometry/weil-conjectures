/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
import WeilConjectures.PoincareDuality.PodReindexCoefficientTransition.PodReindexingTensorCoefficientTransitionCore
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionTensor

/-! # Scalar compatibility of fixed normalized tensor reindexing

For fixed normalized completion and tensor reindexing comparisons at coefficient fields `E` and
`L`, there is a coefficient transition along `ι : E →ₐ[ℚ_[l]] L` satisfying all its laws.

## Implementation details

On completed module sheaves, scalar extension commutes with reindexing by balanced tensor
associativity, normalized to send `a ⊗ x` to the original `a ⊗ x` after the coefficient
identification. The normalized scalar completion realizations at `X` and `Y` give the source and
target of the transition. The reduction square is balanced tensor associativity on simultaneous
quotient resolutions, the limit square is the diagonal scalar comparison on both Roos
coordinates, and on tensor towers the two scalar/reindexing paths agree on homogeneous pure
tensors; applying the Roos realization and descending gives the laws.

## References

* Stacks Project, Tags 03EL, 06YY, 07A4, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- For fixed normalized completion and tensor reindexing comparisons `D, T` at `E` and
`D', T'` at `L` along an isomorphism `g`, there exists a coefficient transition along `ι` from
`D` to `D'` satisfying the transition laws with respect to `T` and `T'`. -/
theorem podReindexingTensorCoefficientTransition
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T') :
    ∃ S : PodReindexCoefficientTransition l E L ι g D D',
      S.Laws l E L ι g D D' T T' := by
  obtain ⟨S, hS⟩ := podReindexingTensorCoefficientTransition_core l E g D hD T hT L ι D' hD' T' hT'
  refine ⟨S, ?_⟩
  rcases hS with ⟨hpure, hred, hlim⟩
  have hten := podReindexingTensorCoefficientTransition_tensor l E g D hD T hT L ι D' hD' T' hT' S
    ⟨hpure, hred, hlim⟩
  exact ⟨hpure, hred, hlim, hten⟩

end WeilConjectures
