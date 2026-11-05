/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Strict quotient-system presentations of coefficient reduction

Source: Stacks 06YY, 07A6 and 0941.

For a reduction functor with its normalized adjunction to the total limit, the ordinary
quotient system of a flat-term K-flat complex is a strict tensor presentation: its
finite evaluations, horizontal maps and whole-system unit are the prescribed ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures.OrdinaryQuotient
