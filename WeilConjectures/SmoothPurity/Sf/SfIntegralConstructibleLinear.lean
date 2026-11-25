/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Constant-section linearity of the intrinsic integral constructible category

The ambient constant-section action is the published `integralCoefficientLinear`.
The full subcategory here is the currently recorded `sfIntegralConstructibleCategory`,
with the triangulation of `SfIntegralConstructibleTriangulated`. Legacy declarations
remain available through the public import.

## Implementation details

The completed coefficient ring `𝒪_E` is the inverse limit of its finite quotients, so each
`a ∈ 𝒪_E` gives compatible constant sections `c_U(a)` (`integralScalarConstant`). Setting
`(a f)_U(x) = c_U(a) f_U(x)` makes the module-sheaf category linear; localization and shifts
are then linear, giving `integralCoefficientLinear`, which restricts to the full constructible
subcategory and its inherited shifts.

## References

* Stacks Project, Tags 03CW, 03DA, 05RU and 09MJ.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The published ambient constant-section action, exposed at the source-category
abbreviation used by the intrinsic constructible predicate. The two module categories
and their standard derived localizations are definitionally identical. -/
noncomputable instance sfIntegralCoefficientLinear :
    Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (scalarReductionSource l E Y)) :=
  integralCoefficientLinear l E Y

/-- The intrinsic full subcategory inherits precisely the ambient constant-section
module structure on Hom groups, including its bilinear composition. -/
noncomputable instance sfIntegralConstructibleLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E Y) :=
  Linear.fullSubcategory (sfIntegralConstructible l E Y)

/-- The ambient and intrinsic integral constructible categories are linear for the
canonical constant-section action, and all their integer shifts are linear. The
subcategory has the inherited triangulation and its inclusion preserves scalars. -/
theorem sfIntegralConstructible_linear :
    (∀ (a : Padic.coefficientExtensionIntegers l E)
      (K L : DerivedCategory (scalarReductionSource l E Y)) (f : K ⟶ L),
      a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) ∧
    (∀ n : ℤ, Functor.Linear (Padic.coefficientExtensionIntegers l E)
      (shiftFunctor (DerivedCategory (scalarReductionSource l E Y)) n)) ∧
    Functor.Linear (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructible l E Y).ι ∧
    (∀ n : ℤ, Functor.Linear (Padic.coefficientExtensionIntegers l E)
      (shiftFunctor (sfIntegralConstructibleCategory l E Y) n)) := by
  refine ⟨?_, ?_, inferInstance, ?_⟩
  · exact (integralCoefficientLinear_existsUnique l E Y).exists.choose_spec
  · intro n
    exact integralCoefficientShift_linear l E Y n
  · intro n
    let P := sfIntegralConstructible l E Y
    let R := Padic.coefficientExtensionIntegers l E
    let : (shiftFunctor (DerivedCategory (scalarReductionSource l E Y)) n).Linear R :=
      integralCoefficientShift_linear l E Y n
    let : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
      Functor.linear_of_iso R (P.ι.commShiftIso n).symm
    constructor
    intro X Z f a
    apply P.ι.map_injective
    rw [P.ι.map_smul]
    exact (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul a f

/-- Every inherited integer shift is linear for the canonical constant-section action.
This is the final clause of `sfIntegralConstructible_linear`. -/
noncomputable instance sfIntegralConstructibleShift_linear (n : ℤ) :
    (shiftFunctor (sfIntegralConstructibleCategory l E Y) n).Linear
      (Padic.coefficientExtensionIntegers l E) :=
  (sfIntegralConstructible_linear l E Y).2.2.2 n

end WeilConjectures
