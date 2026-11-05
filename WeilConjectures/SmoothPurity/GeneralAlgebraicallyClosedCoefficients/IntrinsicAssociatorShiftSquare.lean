/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages

import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicScalarNormalizationFormulas

/-! # The intrinsic scalar associator commutes with integer shifts

Source: blueprint order 1462, common-stage shift clause, and
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`,
exact derived scalar composition, with the intrinsic normalization specified in
`SfScalarExtensionComposition.lean` and `GeneralAlgebraicallyClosedCoefficientStages.lean`
(blueprint: lem-pur-intrinsic-associator-shift-square).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TensorProduct

namespace WeilConjectures.GeneralAlgebraicallyClosedCoefficients

open CategoryTheory.Limits
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the coefficient constructions behind their published normalization interfaces.
attribute [local irreducible] ScalarLocalization.composition
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] sfIntegralOrdinaryComparison sfIntegralScalarComp
  sfRationalScalarComp sfRationalTriangulationDatum sfRationalScalarExtension

section Integral

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

attribute [local instance] normalizedIntegralShift

attribute [local irreducible] normalizedComparison

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

end Integral

section LocalizationSquare

variable {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
  {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Preadditive C₀] [Preadditive C₁] [Preadditive C₂]
  [Linear R₀ C₀] [Linear R₁ C₁] [Linear R₂ C₂]
  [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [(shiftFunctor C₀ (1 : ℤ)).Additive] [(shiftFunctor C₁ (1 : ℤ)).Additive]
  [(shiftFunctor C₂ (1 : ℤ)).Additive]
  [(shiftFunctor C₀ (1 : ℤ)).Linear R₀] [(shiftFunctor C₁ (1 : ℤ)).Linear R₁]
  [(shiftFunctor C₂ (1 : ℤ)).Linear R₂]
  (p₀ : R₀) (p₁ : R₁) (p₂ : R₂)

local notation "D₀" => ScalarLocalization R₀ C₀ p₀
local notation "D₁" => ScalarLocalization R₁ C₁ p₁
local notation "D₂" => ScalarLocalization R₂ C₂ p₂
local notation "Q₀" => ScalarLocalization.localization R₀ C₀ p₀
local notation "Q₁" => ScalarLocalization.localization R₁ C₁ p₁
local notation "Q₂" => ScalarLocalization.localization R₂ C₂ p₂

variable [s₀ : HasShift (ScalarLocalization R₀ C₀ p₀) ℤ]
  [s₁ : HasShift (ScalarLocalization R₁ C₁ p₁) ℤ]
  [s₂ : HasShift (ScalarLocalization R₂ C₂ p₂) ℤ]

end LocalizationSquare

end WeilConjectures.GeneralAlgebraicallyClosedCoefficients
