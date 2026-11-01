/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteFirstRootChart
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
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

import WeilConjectures.SmoothPurity.PurityFiniteSetting.FinitePublishedRootChartPower
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootChartPower
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-root-tensor-presentation)

## Main declarations

- `finiteTensorPositivePresentation`
- `finiteTensorPositiveReduction`
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

/-- The existing shifted positive root chart, with its coefficient-unit comparison.
Source: def-pur-finite-reduction-root-charts
(blueprint: def-pur-finite-root-tensor-presentation). -/
abbrev finiteTensorDiagonalChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :=
  P.finiteReductionPowerTrivialization T ζ hζ d ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (finiteReductionComparisonUnitChart P.Coefficient T)

/-- The shared type of the root-normalized positive presentation comparison.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-root-tensor-presentation). -/
def FiniteTensorPositivePresentationType (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (d : ℕ) :=
  P.diagonalTwist T d ≅ (P.finiteTensorFixedLine T d)⟦2 * (d : ℤ)⟧

private theorem chart_ratio_eq {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (s s' : A ≅ B) (t t' : D ≅ B) (r : ℕ)
    (hs : s'.hom = r • s.hom) (ht : t'.hom = r • t.hom) :
    s ≪≫ t.symm = s' ≪≫ t'.symm := by
  apply Iso.ext
  apply (cancel_mono t'.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [ht, hs]
  simp only [Preadditive.comp_nsmul, Iso.inv_hom_id, Category.comp_id]

/-- Root-normalized equality of the integral-reduced and shifted positive presentations.
It is fixed in every primitive-root chart, including the coefficient-unit stage.
Source: blueprint proof Step 8; def-pur-finite-reduction-root-charts
(blueprint: def-pur-finite-root-tensor-presentation).
Proof: compare both sides with the shifted coefficient unit using their root charts.
Their composite gives the isomorphism. Changing a primitive root multiplies both
charts by the same d-th power, so the composite is independent of that root.
A primitive root exists over k and each chart is invertible, proving uniqueness. -/
theorem existsUnique_finiteTensorPositivePresentation (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d : ℕ) :
    ∃! e : P.FiniteTensorPositivePresentationType T d,
      ∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent),
        HEq e (P.finiteTensorDiagonalChart T d ζ hζ ≪≫
          (shiftFunctor _ (2 * (d : ℤ))).mapIso
            (P.finiteTensorPositiveChart T ζ hζ d).symm) := by
  classical
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let s (η : P.field.k) (hη : IsPrimitiveRoot η P.diagonalExponent) :=
    P.finiteTensorDiagonalChart T d η hη
  let t (η : P.field.k) (hη : IsPrimitiveRoot η P.diagonalExponent) :=
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (P.finiteTensorPositiveChart T η hη d)
  refine ⟨s ζ hζ ≪≫ (t ζ hζ).symm, ?_, ?_⟩
  · intro η hη
    obtain ⟨a, _, ha⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
    have hs : (s η hη).hom = a ^ d • (s ζ hζ).hom := by
      dsimp only [s, finiteTensorDiagonalChart, Iso.trans_hom]
      rw [P.finiteReductionPowerTrivialization_pow T d a ζ η hζ hη ha.symm,
        Preadditive.nsmul_comp]
    have ht : (t η hη).hom = a ^ d • (t ζ hζ).hom := by
      dsimp only [t, Functor.mapIso_hom]
      rw [P.finiteTensorPositiveChart_pow T d a ζ η hζ hη ha.symm,
        Functor.map_nsmul]
    exact heq_of_eq (chart_ratio_eq (s ζ hζ) (s η hη) (t ζ hζ) (t η hη) (a ^ d) hs ht)
  · intro e he
    exact (eq_of_heq (he ζ hζ)).trans (by
      simp only [s, t, Functor.mapIso_symm]
      rfl)

/-- Canonical change between the two recorded presentations of the same positive line.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-root-tensor-presentation). -/
def finiteTensorPositivePresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ) :
    P.FiniteTensorPositivePresentationType T d :=
  (P.existsUnique_finiteTensorPositivePresentation T d).exists.choose

/-- Signed-line reduction in the published shifted positive presentation.
This is constructed from the actual line comparison and the native scalar shift.
Source: blueprint proof Steps 4, 6 and 8
(blueprint: def-pur-finite-root-tensor-presentation). -/
abbrev finiteTensorPositiveReduction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d : ℕ) :=
  (P.finiteTensorReduction m hm hmn T).mapIso (P.finiteTensorPositivePresentation T d) ≪≫
    (P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (P.finiteTensorLineComparison m hm hmn T d) ≪≫
    ((P.finiteReductionSetting m hm).finiteTensorPositivePresentation T d).symm

end WeilConjectures.PurityFiniteSetting
