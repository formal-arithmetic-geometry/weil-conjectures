/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions


/-! Integral line tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- The completion comparison is invertible on a derived-complete object.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-sf-integral-line-tensor-comparison-iso).

Proof: take a flat-term K-flat representative P of C. The identity-extension
specialization of finiteFreeCompletedScalarComparison makes the prescribed quotient
completion augmentation of P invertible. Tensor by T is an exact equivalence, with
inverse tensor by its dual: after a cover trivializing T both composites are the
identity, so the local identifications glue. This equivalence preserves countable
products and mapping cones. The balancing isomorphisms identify the tower of the
tensor complex with tensor by T of the original restricted quotient tower. These
isomorphisms preserve every quotient transition and the augmentation x ↦ 1 tensor x.
Consequently the augmentation of P tensor T is tensor by T of the invertible
augmentation of P. It is invertible after localization. The representative
normalization defining completionUnit identifies this augmentation with exactly
integralLineComparison, including its zero shifted component. Conjugation by the
representative isomorphisms proves the displayed assertion. No boundedness or
constructibility assumption is used. -/
theorem integralLineTensorComparison_iso
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : D l E X none) (hC : IsComplete l E X none C)
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    IsIso ((integralLineComparison l E X).app (C, T)) := by
  sorry


end WeilConjectures
