/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! Abstract rational scalar associator compatibility with normalized shifts.

Source: the tensor-generator and localization step of the intrinsic associator-shift
argument (blueprint: lem-pur-intrinsic-associator-shift-square).
The abstract coefficient-field statement isolates the only component calculation
that is expensive when specialized to finite `Shrink` models; the specialization in
the owning module only transports this statement across the coefficient-inclusion
equality. The generic localization square below is the one proved privately in
`IntrinsicAssociatorShiftSquare`, which cannot be imported here (it imports the
general-stage specialization, which imports the owning module).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace WeilConjectures

attribute [local irreducible] sfIntegralScalarComp
  sfRationalTriangulationDatum sfRationalScalarExtension

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

end WeilConjectures
