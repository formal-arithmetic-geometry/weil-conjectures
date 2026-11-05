/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationExpressions
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.SmoothPurity.Normalized.NormalizedCompletionRealization
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatNormalization
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization

/-! # Simultaneous primitive models for completed operations

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4); blueprint
main-20261015, order 2232, coefficient twists; explicit coherent-counit refinement
in original proof steps 1--6 of completed-operation substitution
(blueprint: lem-pur-normalized-completed-operation-models).

All comparisons live in the ordinary derived category of the ringed sequence
site before restriction or total derived limit. The natural-number index n
means positive quotient exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

end WeilConjectures.CompletedOperations
