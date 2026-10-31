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

/-- A binary representative square, formulated before specializing its categorical
instances. It is the full tensor-counit equation, not equality of endpoint objects.
Source: Stacks 07A4 and 0FPT
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def finiteTensorBinaryRepresentativeSquare
    {C₁ : Type c₁} [Category.{v₁} C₁] [MonoidalCategory C₁]
    {C₂ : Type c₂} [Category.{v₂} C₂] [MonoidalCategory C₂]
    {D₁ : Type d₁} [Category.{w₁} D₁] [MonoidalCategory D₁]
    {D₂ : Type d₂} [Category.{w₂} D₂] [MonoidalCategory D₂]
    (QA : C₁ ⥤ D₁) [QA.LaxMonoidal] (QB : C₂ ⥤ D₂) [QB.LaxMonoidal]
    (F : C₁ ⥤ C₂) (Q : D₁ ⥤ D₂) (h : Q.CoreMonoidal)
    (c : ∀ X : C₁, Q.obj (QA.obj X) ⟶ QB.obj (F.obj X))
    (δ : ∀ X Y : C₁, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y) (X Y : C₁) : Prop :=
  Q.map (Functor.LaxMonoidal.μ QA X Y) ≫ c (X ⊗ Y) ≫ QB.map (δ X Y) =
    (h.μIso (QA.obj X) (QA.obj Y)).inv ≫ (c X ⊗ₘ c Y) ≫
      Functor.LaxMonoidal.μ QB (F.obj X) (F.obj Y)

/-- The symmetry square for a fixed strong monoidal comparison.
Source: blueprint proof Step 2, Stacks 0FPT
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def FiniteTensorSymmetrySquare
    {C : Type c₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d₁} [Category.{w₁} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) (h : F.CoreMonoidal) (X Y : C) : Prop :=
  F.map (β_ X Y).hom ≫ (h.μIso Y X).inv =
    (h.μIso X Y).inv ≫ (β_ (F.obj X) (F.obj Y)).hom

/-- Compatibility of a binary comparison with two specified tensor-shift maps.
Specialization supplies exactly the published native derived tensor-shift maps.
Source: blueprint proof Step 6, Stacks 0FNH
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def FiniteTensorShiftSquare
    {C : Type c₁} [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    {D : Type d₁} [Category.{w₁} D] [MonoidalCategory D] [HasShift D ℤ]
    (F : C ⥤ D) (σ : ∀ s : ℤ, shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    (h : F.CoreMonoidal) (X Y : C) (a b : ℤ)
    (sA : X⟦a⟧ ⊗ Y⟦b⟧ ≅ (X ⊗ Y)⟦a + b⟧)
    (sB : (F.obj X)⟦a⟧ ⊗ (F.obj Y)⟦b⟧ ≅ (F.obj X ⊗ F.obj Y)⟦a + b⟧) : Prop :=
  F.map sA.hom ≫ (σ (a + b)).hom.app (X ⊗ Y) ≫
      ((h.μIso X Y).inv)⟦a + b⟧' =
    (h.μIso (X⟦a⟧) (Y⟦b⟧)).inv ≫
      ((σ a).hom.app X ⊗ₘ (σ b).hom.app Y) ≫ sB.hom

/-- The scalar-shift, binary tensor, and line-map composite with categorical instances
shared before specialization. The shift input is the specified actual scalar shift.
Source: blueprint proof Step 6
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def finiteTensorTwistShiftComponent
    {C : Type c₁} [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    {D : Type d₁} [Category.{w₁} D] [MonoidalCategory D] [HasShift D ℤ]
    (F : C ⥤ D) (h : F.CoreMonoidal) (X A : C) (B : D) (b : F.obj A ≅ B) (s : ℤ)
    (t : F.obj ((X ⊗ A)⟦s⟧) ≅ (F.obj (X ⊗ A))⟦s⟧) :
    F.obj ((X ⊗ A)⟦s⟧) ≅ (F.obj X ⊗ B)⟦s⟧ :=
  t ≪≫ (shiftFunctor D s).mapIso
    ((h.μIso X A).symm ≪≫ tensorIso (Iso.refl _) b)

/-- The actual single-complex tensor arrow followed by a prescribed sheaf product.
Source: blueprint proof Step 5, canonical localization tensor comparison
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def finiteTensorSingleProductHom
    {C : Type c₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (_root_.DerivedCategory C)]
    [(_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    (L M N : C) (p : L ⊗ M ⟶ N) :=
  ProEtale.cupSingleTensorMap L M ≫ (_root_.DerivedCategory.singleFunctor C 0).map p

/-- The actual single-complex tensor comparison followed by a given sheaf arrow.
The heterogeneous form shares the categorical instances before specialization.
Source: blueprint proof Step 5, canonical single-complex localization comparison
(blueprint: def-pur-finite-tensor-comparison-equations). -/
def FiniteTensorSingleProductNormalized
    {C : Type c₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (_root_.DerivedCategory C)]
    [(_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    (L M N : C) (p : L ⊗ M ⟶ N) {α : Type w₁} (a : α) : Prop :=
  HEq a (finiteTensorSingleProductHom L M N p)

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
