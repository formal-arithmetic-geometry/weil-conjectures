module

public import Sheaf.Paper.NativeConstantSupportModel
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # All limits for constant scalar restriction

The all-shaped ordinary limit clause is isolated from the K-injective clause
of the scalar-limit restriction foundation.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The constant-coefficient restriction on strict towers preserves the
ordinary inverse-limit shape.  This is the limit component of
`scalarLimitRestriction_exact`; its proof is the pointwise sheaf-limit
argument for restriction of scalars.
Source: Stacks 03DA and 0941.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-limits).
Proof: compute limits of sheaves of modules pointwise, use the restriction of
scalars functor on modules, and transport the resulting limit cone through
the constant-tower construction.
-/
theorem scalarRestriction_preservesLimits (W : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (constantRestriction l E W) := by
  sorry

end WeilConjectures.PurStrictScalar
