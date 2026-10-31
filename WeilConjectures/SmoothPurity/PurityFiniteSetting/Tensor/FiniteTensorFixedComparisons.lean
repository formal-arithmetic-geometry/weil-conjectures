/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteFirstRootChart
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootTensorPresentation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-! # Canonical finite-reduction comparisons in fixed-scalar coordinates

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2, expanded Steps 7--9.
(blueprint: def-pur-finite-tensor-fixed-comparisons)

## Main declarations

- `finiteTensorPullbackComparison`
- `finiteTensorPuritySourceComparison`
- `finiteTensorPurityTargetComparison`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- Inverse-realization unit identifies the published intrinsic pullback coordinates.
Source: def-pur-finite-reduction-comparisons
(blueprint: def-pur-finite-tensor-fixed-comparisons). -/
def finiteTensorPullbackModel (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : _root_.DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReductionPullback f).obj ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K) ≅
      (sfIntrinsicDerivedEquivalence X P.Ring).functor.obj ((P.smoothPurityPullback f).obj K) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    ((P.smoothPurityPullback f).mapIso
      ((sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.symm.app K))

/-- The actual scalar-adjunction mate, transported through the specified realization.
No pullback comparison is chosen independently of the recorded coefficient square.
Source: blueprint proof Step 7; def-pur-finite-reduction-comparisons
(blueprint: def-pur-finite-tensor-fixed-comparisons). -/
def finiteTensorPullbackComparison (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorReduction m hm hmn X).obj ((P.smoothPurityPullback f).obj K) ≅
      ((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
        ((P.finiteTensorReduction m hm hmn Y).obj K) :=
  let e₀ := (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
    (P.finiteReductionRingHom m hm hmn) X).symm.app ((P.smoothPurityPullback f).obj K)
  let e₁ := (P.finiteReduction m hm hmn X).mapIso (P.finiteTensorPullbackModel f K).symm
  let e₂ := P.finiteReductionPullbackComparison m hm hmn f
    ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K)
  let e₃ := ((P.finiteReductionSetting m hm).finiteReductionPullback f).mapIso
    ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y).app K)
  let e₄ := (P.finiteReductionSetting m hm).finiteTensorPullbackModel f
    ((P.finiteTensorReduction m hm hmn Y).obj K)
  let e₀₁ := e₀ ≪≫ e₁
  let e₂₃ := e₂ ≪≫ e₃
  let e₀₃ := e₀₁ ≪≫ e₂₃
  let e₀₄ := e₀₃ ≪≫ e₄
  (sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.preimageIso
    e₀₄

/-- The input-realization unit for the published shifted pullback presentation.
Source: def-pur-finite-reduction-comparisons
(blueprint: def-pur-finite-tensor-fixed-comparisons). -/
def finiteTensorSourceModel (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :=
  (sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    ((P.compositionTwistShift X d).mapIso
      ((P.smoothPurityPullback f).mapIso
        ((sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.symm.app K)))

/-- Transport of exactly the recorded root-normalized source comparison, by the
scalar presentation and the realization units. Source: blueprint proof Steps 7--9
(blueprint: def-pur-finite-tensor-fixed-comparisons). -/
def finiteTensorPuritySourceComparison (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorReduction m hm hmn X).obj
        ((P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj K)) ≅
      ((P.finiteReductionSetting m hm).compositionTwistShift X d).obj
        (((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
          ((P.finiteTensorReduction m hm hmn Y).obj K)) :=
  let e₀ := (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
    (P.finiteReductionRingHom m hm hmn) X).symm.app
      ((P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj K))
  let e₁ := (P.finiteReduction m hm hmn X).mapIso (P.finiteTensorSourceModel f d K).symm
  let e₂ := P.finiteReductionSourceComparison m hm hmn f d
    ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K)
  let e₃ := ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).mapIso
    ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y).app K)
  let e₄ := (P.finiteReductionSetting m hm).finiteTensorSourceModel f d
    ((P.finiteTensorReduction m hm hmn Y).obj K)
  let e₀₁ := e₀ ≪≫ e₁
  let e₂₃ := e₂ ≪≫ e₃
  let e₀₃ := e₀₁ ≪≫ e₂₃
  let e₀₄ := e₀₃ ≪≫ e₄
  (sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.preimageIso
    e₀₄

/-- Independently constructed target comparison: binary tensor reduction, the
recorded pullback mate, and the actual positive line reduction in that order.
Source: blueprint proof Steps 2, 7--9
(blueprint: def-pur-finite-tensor-fixed-comparisons). -/
def finiteTensorPurityTargetComparison (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :=
  ((P.finiteTensorCore m hm hmn X).μIso
      ((P.smoothPurityPullback f).obj K) (P.diagonalTwist X d)).symm ≪≫
    tensorIso (P.finiteTensorPullbackComparison m hm hmn f K)
      (P.finiteTensorPositiveReduction m hm hmn X d)

end WeilConjectures.PurityFiniteSetting
