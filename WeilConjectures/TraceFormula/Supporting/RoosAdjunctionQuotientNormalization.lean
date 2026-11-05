/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitStrictQuotientModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Simultaneous Roos, counit and strict quotient-unit normalization

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
whole-system adjunction and quotient-unit refinements extracted from the integral
trace-transport construction (blueprint: lem-trf-roos-adjunction-quotient-normalization).

The coefficient field F is arbitrary: apply this statement to each of E, L and M.
No distinctness or compatibility between different coefficient fields is required.
Index n denotes the positive quotient exponent n+1. The site and coefficient
universes remain independent. All categories are ordinary unbounded derived categories.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

section Normalization

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (W : Scheme.{t})
  {S : CoefficientDerivedSystemCalculus l F W}
  {M : CompletionUnit.OrdinaryModel l F W}
  (D : CompletionUnit.DerivedModel l F W S M)

end Normalization

end WeilConjectures
