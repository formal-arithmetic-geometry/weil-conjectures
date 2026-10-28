/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.PodCompletionTensorNormalization

/-! # Strict Roos realization for normalized tensor reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict Roos realization supplies the Model equation before Canonical.

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-roos-strict).

Proof: choose simultaneous flat-term K-flat representatives. The finite tensor
reductions identify with total tensors of quotient complexes. The forward generator
law identifies the strict tower with the quotient pullback/tensor map, and tower
naturality makes this an identity of coherent systems. The two Roos coordinates of
D transport the identity through localization to Model. The finite and limit model
laws complete the transport; zero representatives and empty schemes are included.
-/
theorem podReindexingTensorRoosNormalization_model_iff_canonical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    (hnat : PodCompletedTensorReindex.TowerNaturality l E g D T) :
    PodCompletedTensorReindex.Model l E g D T ∧
      PodCompletedTensorReindex.Canonical l E g D T := by
  sorry

end WeilConjectures
