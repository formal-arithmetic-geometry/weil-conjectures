/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShiftsCore
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedSquares

/-! # Signed shifts of fixed normalized tensor reindexing

Source: Stacks 07A4, 0941. -/

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

/-- Signed shifts of the same quotient-normalized completion and tensor maps.
Source: Stacks 011G, 07A4, 0941. -/
theorem podReindexingTensorSignedShifts
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ SY : PodTensorSignedShift l E Y, ∃ SX : PodTensorSignedShift l E X,
      PodReindexSignedShifts l E g D T SY SX := by
  obtain ⟨SY, SX, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ :=
    podReindexingTensorSignedShifts_core l E g D hD T hT
  have hs := podReindexingTensorSignedShifts_tensorSquares l E g D hD T hT SY SX h₅ h₆ h₇ h₈
  refine ⟨SY, SX, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, ?_⟩
  intro M N M' N' r a b
  exact ⟨hs.1 M N M' N' r a b, hs.2 M N M' N' r a b⟩

end WeilConjectures
