/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShiftModels
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShiftCompatibility

/-! # Core signed-shift models for tensor reindexing -/

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

/-- There exist signed tensor shift structures on the source and target satisfying the
`Generators` and `Model` laws, such that the reduction and limit comparisons of `D` commute with
shifts and the Roos models satisfy the limit signed-shift identities.

See [Stacks, Tags 07A4, 0941]. -/
theorem podReindexingTensorSignedShifts_core
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ SY : PodTensorSignedShift l E Y, ∃ SX : PodTensorSignedShift l E X,
      NatTrans.CommShift D.reduction.hom ℤ ∧
      NatTrans.CommShift D.limit.hom ℤ ∧
      PodLimitSignedShift l E Y D.sourceRoos D.shiftSource ∧
      PodLimitSignedShift l E X D.targetRoos D.shiftTarget ∧
      SY.Generators l E ∧ SX.Generators l E ∧
      SY.Model l E D.shiftSource ∧ SX.Model l E D.shiftTarget := by
  obtain ⟨SY, SX, hSYg, hSXg, hSYm, hSXm⟩ :=
    podReindexingTensorSignedShiftModels l E g D hD T hT
  obtain ⟨hred, hlim, hY, hX⟩ :=
    podReindexingTensorSignedShiftCompatibility l E g D hD T hT SY SX
      hSYg hSXg hSYm hSXm
  exact ⟨SY, SX, hred, hlim, hY, hX, hSYg, hSXg, hSYm, hSXm⟩

end WeilConjectures
