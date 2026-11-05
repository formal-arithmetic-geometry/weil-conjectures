/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Strict presentations of reduction through the ordinary quotient system

Source: Stacks 06YY, 07A4, 07A6 and 0941.

A strict reduction presentation `e : reduction (Q P) ≅ Q C` whose adjunct is the
localization of a strict map `z : P ⟶ lim C` is the localization of the ordinary
transpose `g : quotient P ⟶ C` of `z`, composed with the universal comparison `ε`.
The finite evaluations of `g` are the normalized evaluation isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures.OrdinaryQuotient

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

namespace OrdinaryQuotient

end OrdinaryQuotient

namespace OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end OrdinaryQuotient

end WeilConjectures
