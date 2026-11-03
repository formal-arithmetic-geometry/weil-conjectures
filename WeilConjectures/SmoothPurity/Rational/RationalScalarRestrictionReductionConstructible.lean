/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Finite reductions after rational scalar restriction

Exact restriction identifies each finite reduction with restriction of a finite
coefficient reduction of the original object. The same finite stratifications,
interval, and local models are retained after restriction of scalars. This is
separated from completeness because it is a finite-level constructibility
assertion.
(blueprint: lem-sf-rational-scalar-restriction-reduction-constructible)
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures

open AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- Restricted reductions remain intrinsically constructible in one common interval.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
Proof: use the finite quotient square induced by the completed coefficient map and
exactness of scalar restriction to identify homology of every E-reduction with a
restricted F-reduction. Reuse the F object's finite stratifications and degree
interval. Restriction of each finite constant local model remains finite over the
source quotient ring, and the sheafification comparison is sectionwise. Taking
the interval supplied by `K.property` gives the common bounds for all levels.
No Noetherian hypothesis on `W` is used.
(blueprint: lem-sf-rational-scalar-restriction-reduction-constructible) -/
theorem rationalScalarDerivedRestriction_reduction_constructible
    (K : sfIntegralConstructibleCategory l F W) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
          ((scalarReductionDerivedExtension l E W n).obj
            ((rationalScalarDerivedRestriction l E F ι W).obj K.obj)) ∧
      proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E W n).obj
            ((rationalScalarDerivedRestriction l E F ι W).obj K.obj)) ⊆ Set.Icc a b := by
  sorry

end WeilConjectures
