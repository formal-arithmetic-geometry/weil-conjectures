/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteFirstRootChart
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
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

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartRecursion
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartFrameExt

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-positive-root-charts)

## Main declarations

- `finiteTensorSheafCharts`
- `finiteTensorPositiveChart`
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

universe c v w

private theorem singleUnitChart_existsUnique
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L : C) (a : (_root_.DerivedCategory.singleFunctor C 0).obj L ≅
      𝟙_ (_root_.DerivedCategory C)) :
    ∃! e : L ≅ 𝟙_ C, FiniteTensorSingleUnitChartNormalized C L e a := by
  let F := _root_.DerivedCategory.singleFunctor C 0
  let c := _root_.DerivedCategory.singleFunctorObjUnitIso C
  let e := F.preimageIso (a ≪≫ c.symm)
  have he : F.mapIso e = a ≪≫ c.symm := by
    ext
    simp [e]
  have hn : FiniteTensorSingleUnitChartNormalized C L e a := by
    apply heq_of_eq
    unfold finiteTensorSingleUnitChart
    change F.mapIso e ≪≫ c = a
    rw [he]
    simp
  refine ⟨e, hn, ?_⟩
  intro b hb
  apply F.mapIso_injective
  change HEq (finiteTensorSingleUnitChart C L b) a at hb
  unfold finiteTensorSingleUnitChart at hb
  have hb' : F.mapIso b ≪≫ c = a := eq_of_heq hb
  calc
    F.mapIso b = (F.mapIso b ≪≫ c) ≪≫ c.symm := by simp
    _ = a ≪≫ c.symm := by rw [hb']
    _ = F.mapIso e := he.symm

/-- The ordinary sheaf chart type, before taking its single complex.
Source: blueprint proof Step 8, locally free coefficient lines
(blueprint: def-pur-finite-positive-root-charts). -/
def FiniteTensorSheafChartType (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  P.finiteTensorFixedSheaf T d ≅
    𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))

/-- The ordinary first chart has the exact prescribed single-complex realization.
Source: blueprint proof Step 8, exact single-complex realization
(blueprint: def-pur-finite-positive-root-charts). -/
def FiniteTensorFirstSheafChartNormalized (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (e : P.FiniteTensorSheafChartType T 1) :
    Prop :=
  FiniteTensorSingleUnitChartNormalized _ (P.finiteTensorFixedSheaf T 1) e
    (P.finiteTensorFirstChart T ζ hζ)

/-- The first sheaf chart is exactly the specified derived root chart on single complexes.
Source: blueprint proof Step 8, exact single-complex realization
(blueprint: def-pur-finite-positive-root-charts).
Proof: both endpoints of the specified first chart are degree-zero singles, using
its native single/unit comparison. Full faithfulness of the single functor lifts
the chart uniquely to an ordinary sheaf isomorphism. -/
theorem existsUnique_finiteTensorFirstSheafChart (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    ∃! e : P.FiniteTensorSheafChartType T 1,
      P.FiniteTensorFirstSheafChartNormalized T ζ hζ e := by
  exact singleUnitChart_existsUnique (P.finiteTensorFixedSheaf T 1)
    (P.finiteTensorFirstChart T ζ hζ)

/-- The normalized degree-one chart before passing to the derived category.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-positive-root-charts). -/
def finiteTensorFirstSheafChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) : P.FiniteTensorSheafChartType T 1 :=
  (P.existsUnique_finiteTensorFirstSheafChart T ζ hζ).exists.choose

/-- The coefficient-one section of the native monoidal unit sheaf.
Source: Stacks 00YV, coefficient unit
(blueprint: def-pur-finite-positive-root-charts). -/
def finiteTensorUnitSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt) :
    (𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))).obj.obj
      (Opposite.op V) :=
  (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)

/-- The shared type of the ordinary positive chart family.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-positive-root-charts). -/
def FiniteTensorSheafChartsType (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  ∀ d : ℕ, P.FiniteTensorSheafChartType T d

/-- Every ordered power of the first root generator is sent to the coefficient unit.
Source: blueprint proof Step 8, coherent ordered local bases
(blueprint: def-pur-finite-positive-root-charts). -/
def FiniteTensorSheafChartsNormalized (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (e : P.FiniteTensorSheafChartsType T) :
    Prop :=
  ∀ (d : ℕ) (V : T.ProEt) (b : P.FiniteTensorFrame T V)
        (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
        (x : (P.finiteTensorFixedSheaf T d).obj.obj (Opposite.op V)),
        HEq (P.finiteTensorSection T 1 V x₁) (P.finiteTensorFrameBasis T V b 1) →
        (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x₁ =
          P.finiteTensorUnitSection T V →
        HEq (P.finiteTensorSection T d V x) (P.finiteTensorFrameBasis T V b d) →
        (e d).hom.hom.app (Opposite.op V) x = P.finiteTensorUnitSection T V

/-- Ordered basis powers of the first-root generator determine all positive charts.
Source: blueprint proof Step 8, with signed products from proof Step 5
(blueprint: def-pur-finite-positive-root-charts).
Proof: on a trivializing cover choose the degree-one generator mapped to one by
the specified first chart. Its ordered powers give the positive generators and
the coefficient one is the zero generator. Send each such generator to one.
Changing the local frame multiplies source and target by the same scalar, so the
maps glue uniquely. Their construction agrees with the normalized signed products
on generators, hence gives exactly the ordered positive-power charts. -/
theorem existsUnique_finiteTensorSheafCharts (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    ∃! e : P.FiniteTensorSheafChartsType T,
      P.FiniteTensorSheafChartsNormalized T ζ hζ e := by
  let e₁ := P.finiteTensorFirstSheafChart T ζ hζ
  let e : P.FiniteTensorSheafChartsType T := P.finiteTensorOrdinaryChartRecursion T e₁
  have he : P.FiniteTensorSheafChartsNormalized T ζ hζ e := by
    intro d V b x₁ x hx₁ he₁ hx
    exact P.finiteTensorOrdinaryChartRecursion_normalized T e₁ d V b x₁ x hx₁ he₁ hx
  refine ⟨e, he, ?_⟩
  intro a ha
  funext d
  apply Iso.ext
  apply P.finiteTensorPositiveChart_frame_ext T e₁ d _
  intro V b x₁ x hx₁ he₁ hx
  exact (ha d V b x₁ x hx₁ he₁ hx).trans (he d V b x₁ x hx₁ he₁ hx).symm

/-- Ordinary positive-power charts, fixed on every compatible ordered local basis.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-positive-root-charts). -/
def finiteTensorSheafCharts (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) : P.FiniteTensorSheafChartsType T :=
  (P.existsUnique_finiteTensorSheafCharts T ζ hζ).exists.choose

/-- The actual positive-power chart, obtained from its normalized ordinary sheaf chart.
Source: blueprint proof Step 8, exact single-complex realization
(blueprint: def-pur-finite-positive-root-charts). -/
def finiteTensorPositiveChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (d : ℕ) :=
  finiteTensorSingleUnitChart _ (P.finiteTensorFixedSheaf T d)
    (P.finiteTensorSheafCharts T ζ hζ d)

end WeilConjectures.PurityFiniteSetting
