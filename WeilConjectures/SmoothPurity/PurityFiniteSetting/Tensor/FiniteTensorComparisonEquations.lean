/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-tensor-comparison-equations)

## Main declarations

- `FiniteTensorSymmetrySquare`
- `FiniteTensorShiftSquare`
- `finiteTensorTwistShiftComponent`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

universe c₁ c₂ d₁ d₂ v₁ v₂ w₁ w₂

/-- The degree-zero chart followed by the native derived unit comparison, with all
categorical instances shared before specializing the coefficient sheaf category.
Source: blueprint proof Step 8, native single-complex realization
(blueprint: def-pur-finite-tensor-comparison-equations). -/
@[irreducible] def finiteTensorSingleUnitChart
    (C : Type c₁) [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w₁} C] [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L : C) (e : L ≅ 𝟙_ C) :
    (_root_.DerivedCategory.singleFunctor C 0).obj L ≅
      𝟙_ (_root_.DerivedCategory C) :=
  (_root_.DerivedCategory.singleFunctor C 0).mapIso e ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso C

/-- Agreement with the entire prescribed single/unit chart, before specialization.
Source: blueprint proof Step 8, exact single-complex realization
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def FiniteTensorSingleUnitChartNormalized
    (C : Type c₁) [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w₁} C] [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L : C) (e : L ≅ 𝟙_ C) {α : Type w₁} (a : α) : Prop :=
  HEq (finiteTensorSingleUnitChart C L e) a

end WeilConjectures.PurityFiniteSetting
