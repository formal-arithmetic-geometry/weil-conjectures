/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.PodCompletionReindexSubstitution

/-! # Core data for fixed normalized reindexing substitution

This isolates the construction of the completed-operation model and all its
comparison, substitution, and structural laws. The tensor model and canonical
normalization remain supplied by `PodCompletedTensorReindex.Laws`.
(blueprint: lem-pod-reindexing-tensor-substitution-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The fixed-model part of normalized reindexing substitution.

The construction follows the normalized quotient/Roos presentation: use the
specified calculus, completion and pullback data from `D`, transport the
canonical closed tensor realization to the two integral completed tensors, and
prove the primitive comparison, substitution, and structural laws by the
whole-system counit and expression induction. The two tensor-normalization
fields are deliberately omitted and are supplied by the tensor laws of `T`.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-substitution-core). -/
structure PodReindexingTensorSubstitutionCoreData
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) where
  C : CompletedOperations.Models l E (podReindexLocations X Y)
  qY : integralCompletedTensor l E Y ≅
    IntegralOnSlice.completedTensor l E Y none
  qX : integralCompletedTensor l E X ≅
    IntegralOnSlice.completedTensor l E X none
  calculus_false : C.calculus false = podReindexCalculus l E Y
  calculus_true : C.calculus true = podReindexCalculus l E X
  completion_false : HEq (C.completion false) D.completionSource
  completion_true : HEq (C.completion true) D.completionTarget
  roos_false : C.roos false = D.sourceRoos
  roos_true : C.roos true = D.targetRoos
  pullback : HEq (C.pullback (a := true) (b := false) g).realization D.pullback
  tensor_Y : HEq (qY ≪≫ CompletedOperations.tensorRealization l E C false)
    (pullbackTensorIntegralTensorModel l E Y)
  tensor_X : HEq (qX ≪≫ CompletedOperations.tensorRealization l E C true)
    (pullbackTensorIntegralTensorModel l E X)
  limit : ∀ N : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app
          ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
      D.limit.hom.app N
  comparisonLaws : CompletedOperations.ComparisonLaws.{u, u, 0, 0} l E C
  substitutionLaw : CompletedOperations.SubstitutionLaw.{u, u, 0, 0, 0} l E C
  structuralLaw : CompletedOperations.StructuralLaw.{u, u, 0, 0} l E C

/-- Core normalized model construction.

The proof is the construction described in the declaration above. Its remaining
work is strictly below `PodReindexSubstitution`: it constructs the fixed model,
its realization identifications and all three expression laws, while leaving the
already supplied tensor `Model` and `Canonical` assertions to the caller.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-substitution-core). -/
theorem podReindexingTensorSubstitutionCore
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T) :
    ∃ core : PodReindexingTensorSubstitutionCoreData l E g D,
      True := by
  sorry

end WeilConjectures
