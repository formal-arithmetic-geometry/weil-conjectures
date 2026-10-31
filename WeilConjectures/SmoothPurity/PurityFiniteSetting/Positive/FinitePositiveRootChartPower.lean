/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootLinePowerTransition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartRecursion

/-! # Power equivariance of the integral-reduced positive root charts

Source: finite-reduction-of-purity, Step 2, positive powers of the coefficient line.
(blueprint: lem-pur-finite-positive-root-chart-power).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

universe v w

private theorem singleChart_nsmul
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L : C) (e e' : L ≅ 𝟙_ C) (a : ℕ) (h : e'.hom = a • e.hom) :
    (finiteTensorSingleUnitChart C L e').hom =
      a • (finiteTensorSingleUnitChart C L e).hom := by
  unfold finiteTensorSingleUnitChart
  simp only [Iso.trans_hom, Functor.mapIso_hom, h, Functor.map_nsmul,
    Preadditive.nsmul_comp]

private theorem singleChart_reflect_nsmul
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L : C) (e e' : L ≅ 𝟙_ C) (a : ℕ)
    (h : (finiteTensorSingleUnitChart C L e').hom =
      a • (finiteTensorSingleUnitChart C L e).hom) : e'.hom = a • e.hom := by
  apply (_root_.DerivedCategory.singleFunctor C 0).map_injective
  apply (cancel_mono (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom).mp
  simpa only [finiteTensorSingleUnitChart, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_nsmul, Preadditive.nsmul_comp] using h

private theorem tensor_nsmul_both {C : Type v} [Category.{w} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] {X Y Z W : C}
    (f : X ⟶ Y) (g : Z ⟶ W) (a b : ℕ) :
    (a • f) ⊗ₘ (b • g) = (a * b) • (f ⊗ₘ g) := by
  have hright (f : X ⟶ Y) (b : ℕ) : f ⊗ₘ (b • g) = b • (f ⊗ₘ g) := by
    induction b with
    | zero => simp
    | succ b ih => simp only [succ_nsmul, MonoidalPreadditive.tensor_add, ih]
  have hleft (a : ℕ) : (a • f) ⊗ₘ g = a • (f ⊗ₘ g) := by
    induction a with
    | zero => simp
    | succ a ih => simp only [succ_nsmul, MonoidalPreadditive.add_tensor, ih]
  rw [hright, hleft, smul_smul, Nat.mul_comm]

private theorem sheafCharts_eq_recursion (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteTensorSheafCharts T ζ hζ =
      P.finiteTensorOrdinaryChartRecursion T (P.finiteTensorFirstSheafChart T ζ hζ) := by
  apply (P.existsUnique_finiteTensorSheafCharts T ζ hζ).unique
  · exact (P.existsUnique_finiteTensorSheafCharts T ζ hζ).exists.choose_spec
  · intro d V b x₁ x hx₁ he₁ hx
    exact P.finiteTensorOrdinaryChartRecursion_normalized T _ d V b x₁ x hx₁ he₁ hx

private theorem recursion_nsmul (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e e' : P.FiniteTensorSheafChartType T 1) (a : ℕ) (h : e'.hom = a • e.hom)
    (d : ℕ) :
    (P.finiteTensorOrdinaryChartRecursion T e' d).hom =
      a ^ d • (P.finiteTensorOrdinaryChartRecursion T e d).hom := by
  induction d using Nat.twoStepInduction with
  | zero => simp only [finiteTensorOrdinaryChartRecursion, pow_zero, one_nsmul]
  | one => simpa only [finiteTensorOrdinaryChartRecursion, pow_one] using h
  | more n ih ih' =>
    simp only [finiteTensorOrdinaryChartRecursion, Iso.trans_hom, tensorIso_hom]
    rw [ih', h, tensor_nsmul_both]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, pow_succ]

/-- The positive chart changes by the same scalar power as the ordered root chart.

Source: `thm-pur-finite-reduction-of-purity`, proof Step 2, invertible-twist
compatibility; the ordered basis normalization in
`def-pur-finite-positive-root-charts`.
(blueprint: lem-pur-finite-positive-root-chart-power).

Proof: let N = ell^n. On constant generators the root trivialization at
zeta = eta^a is a times the trivialization at eta. Its inverse at eta is thus
a times its inverse at zeta. The prescribed first-line site comparison is
independent of the root. Exact realization and its coefficient-unit comparison
therefore give the same equation for finiteTensorFirstChart. Full faithfulness
of the degree-zero single functor and the normalization of the first ordinary
chart give that equation for finiteTensorFirstSheafChart as well.
Work on a pro-etale cover where the first root generator supplies a coherent
frame. Under zeta = eta^a its degree-one generator changes by a, so its ordered
d-fold tensor changes by a^d. The positive chart is characterized by sending
these generators to one. Hence its value at eta is a^d times its value at zeta:
verify this on the generator in each frame and extend linearly. Such frames
exist locally since the first site comparison identifies the line with the
root line. The equality glues by the sheaf axiom. At d = 0 both normalized
charts send the coefficient-unit generator to one, and a^0 = 1. Finally the
additive single-complex functor and its fixed unit comparison preserve the
equality, giving the displayed derived-chart formula. The calculation is valid
on empty schemes and uses no finiteness or connectedness of T. -/
theorem finiteTensorPositiveChart_pow (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (d a : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) (h : ζ = η ^ a) :
    (P.finiteTensorPositiveChart T η hη d).hom =
      a ^ d • (P.finiteTensorPositiveChart T ζ hζ d).hom := by
  have hderived : (P.finiteTensorFirstChart T η hη).hom =
      a • (P.finiteTensorFirstChart T ζ hζ).hom := by
    simp only [finiteTensorFirstChart, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [P.finiteReductionRootTrivialization_inv_power T a ζ η hζ hη h,
      Functor.map_nsmul, Functor.map_nsmul]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  have hfirst : (P.finiteTensorFirstSheafChart T η hη).hom =
      a • (P.finiteTensorFirstSheafChart T ζ hζ).hom := by
    apply singleChart_reflect_nsmul _ _ _ _ a
    have hnη := (P.existsUnique_finiteTensorFirstSheafChart T η hη).exists.choose_spec
    have hnζ := (P.existsUnique_finiteTensorFirstSheafChart T ζ hζ).exists.choose_spec
    change HEq (finiteTensorSingleUnitChart _ _
      (P.finiteTensorFirstSheafChart T η hη)) (P.finiteTensorFirstChart T η hη) at hnη
    change HEq (finiteTensorSingleUnitChart _ _
      (P.finiteTensorFirstSheafChart T ζ hζ)) (P.finiteTensorFirstChart T ζ hζ) at hnζ
    rw [eq_of_heq hnη, eq_of_heq hnζ]
    exact hderived
  have hrec : (P.finiteTensorSheafCharts T η hη d).hom =
      a ^ d • (P.finiteTensorSheafCharts T ζ hζ d).hom := by
    rw [sheafCharts_eq_recursion P T η hη, sheafCharts_eq_recursion P T ζ hζ]
    exact recursion_nsmul P T _ _ a hfirst d
  exact singleChart_nsmul _ _ _ _ (a ^ d) hrec

end WeilConjectures.PurityFiniteSetting
