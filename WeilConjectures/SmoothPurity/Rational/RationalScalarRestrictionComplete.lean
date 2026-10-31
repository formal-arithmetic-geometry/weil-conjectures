/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement

/-! # Completeness after rational scalar restriction

The finite coefficient square identifies the PBC restriction with the recorded
completed restriction. The PBC completeness theorem and normalized coefficient
transport then give the SF completeness predicate. The statement is separated
from finite reduction constructibility because it requires no geometric
hypothesis on the scheme.
(blueprint: lem-sf-rational-scalar-restriction-complete)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- Completeness is preserved by the specified completed rational restriction.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
Proof: transport the object to the normalized PBC coefficient presentation using
`integralDetailedTransport`. The finite quotient projection square identifies the
transport of the completed restriction with PBC restriction. Apply
`pbcScalarRestrictionComplete`, then use `purCoefficientModel_predicates` and
transport back through the derived equivalence. The construction is independent
of Noetherian or dimension assumptions on `W`.
(blueprint: lem-sf-rational-scalar-restriction-complete) -/
theorem rationalScalarDerivedRestriction_complete
    (K : sfIntegralConstructibleCategory l F W) :
    IsSfDerivedComplete l E W
      ((rationalScalarDerivedRestriction l E F ι W).obj K.obj) := by
  sorry

end WeilConjectures
