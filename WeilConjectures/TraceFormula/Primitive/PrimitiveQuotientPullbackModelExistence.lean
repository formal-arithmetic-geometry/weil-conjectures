/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientReductionComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison

/-! # Primitive quotient pullback model existence

This is the pullback conjunct split from
`primitiveQuotientRealizationComparisons`.
The comparison tests whole-system adjunction-coherent quotient presentations.
Source: Stacks 099N(5), 06YY and 0941.
(blueprint: lem-trf-primitive-quotient-pullback-model-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
