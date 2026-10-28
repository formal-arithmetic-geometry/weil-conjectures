/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.PodCompletionReindexShifts

/-! # Compatibility of signed tensor shifts with reindexing

This module records the fixed-model compatibility calculation separately from
the construction of the signed tensor shift models.
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

/-- Compatibility of fixed signed tensor shifts with a normalized reindexing.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shifts-core-compatibility-r3).

Proof: the quotient generator formula is preserved by sectionwise relabelling.
The first Roos coordinate is the projection-defined product comparison, while
the second coordinate acquires the common factor `(-1)^r`.  The Roos shift law
in `hD`, together with the representative-model equations of the two shifts,
descends these identities through localization.  The same calculation gives
`CommShift` for the reduction and limit comparisons.  No boundedness, choice of
representatives, or extra coefficient hypothesis is used.
-/
theorem podReindexingTensorSignedShiftCompatibility
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSYg : SY.Generators l E) (hSXg : SX.Generators l E)
    (hSYm : SY.Model l E D.shiftSource) (hSXm : SX.Model l E D.shiftTarget) :
    NatTrans.CommShift D.reduction.hom ℤ ∧
      NatTrans.CommShift D.limit.hom ℤ ∧
      PodLimitSignedShift l E Y D.sourceRoos D.shiftSource ∧
      PodLimitSignedShift l E X D.targetRoos D.shiftTarget := by
  sorry

end WeilConjectures
