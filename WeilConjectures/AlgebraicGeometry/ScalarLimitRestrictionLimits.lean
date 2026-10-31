/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeConstantSupportModel
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
Proof: for any ring sheaf `A`, limits of sheaves of `A`-modules are computed
in presheaves of modules and hence pointwise on underlying abelian presheaves,
so `toSheaf A` preserves inverse-tower limits (`sheafToPresheaf` reflects them).
Restriction of scalars along the constant-to-completed ring map does not change
the underlying abelian sheaf, so `constantRestriction ⋙ toSheaf` is `toSheaf`
of the completed ring and preserves these limits.  Since `toSheaf` of the
constant ring reflects isomorphisms and its source has inverse-tower limits, it
reflects them, so `constantRestriction` preserves inverse-tower limits.
-/
theorem scalarRestriction_preservesLimits (W : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (constantRestriction l E W) := by
  let A := integralConstantRingOfUniverses l E W
  let B := completedIntegralCoefficientSheafUnrestricted l E W
  have h (A : Sheaf (Scheme.ProEt.topology W) RingCat.{u + 1}) :
      PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.toSheaf.{u + 1} A) := by
    have : PreservesLimitsOfShape ℕᵒᵖ
        (SheafOfModules.toSheaf.{u + 1} A ⋙
          sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}) :=
      inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
        (SheafOfModules.forget.{u + 1} A ⋙ PresheafOfModules.toPresheaf A.obj))
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1})
  have := h A
  have := h B
  have : ReflectsLimitsOfShape ℕᵒᵖ (SheafOfModules.toSheaf.{u + 1} A) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape ℕᵒᵖ
      (constantRestriction l E W ⋙ SheafOfModules.toSheaf.{u + 1} A) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.toSheaf.{u + 1} B))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u + 1} A)

end WeilConjectures.PurStrictScalar
