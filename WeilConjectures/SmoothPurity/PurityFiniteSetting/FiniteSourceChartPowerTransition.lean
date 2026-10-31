/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootLinePowerTransition

/-! # Explicit power transition for finite purity source charts

Source: the root-line and ordered tensor calculation in finite reduction of purity.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem orderedPower_hom_nsmul {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [∀ M : C, (T.obj M).Additive]
    [∀ M : C, (T.flip.obj M).Additive]
    (B U : ℕ → C) (L V : C) (z : B 0 ≅ U 0) (t t' : L ≅ V)
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (a : ∀ n : ℕ, (T.obj (U n)).obj V ≅ U (n + 1))
    (c : ℕ) (ht : t'.hom = c • t.hom) (d : ℕ) :
    (finiteReductionOrderedPower T B U L V z t' s a d).hom =
      c ^ d • (finiteReductionOrderedPower T B U L V z t s a d).hom := by
  induction d with
  | zero => simp only [finiteReductionOrderedPower, pow_zero, one_nsmul]
  | succ d ih =>
    simp only [finiteReductionOrderedPower, compositionTensorMapIso,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    change (s d).hom ≫ ((T.flip.obj L).map _ ≫ _) ≫ (a d).hom = _
    rw [ih, ht, Functor.map_nsmul, Functor.map_nsmul]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, smul_smul, pow_succ, Nat.mul_comm]
    rfl

/-- If the old root is the `c`th power of the new root, the new source chart is
`c ^ d` times the old source chart.

Source: blueprint `thm-pur-finite-reduction-of-purity`, Step 2, compatibility of
invertible twists by tensor associativity; Stacks 03PK and 07A4
(blueprint: lem-pur-finite-source-chart-power-transition).

Proof: on constant scalar sections the forward root-line chart sends `a` to
`a tensor ζ`. The equality `ζ = ζ' ^ c` identifies this with `c` times the chart
for `ζ'`, because multiplication of roots is addition in their root module.
Sheafification uniqueness gives equality of the forward charts. Compose with
their inverses: the inverse chart for `ζ'` is `c` times that for `ζ`. The single
complex and shift functors preserve this equality. Induct through the specified
ordered tensor recursion. The zero chart is independent of the root, giving
`c ^ 0 = 1`. At a successor, additivity in each tensor variable multiplies the
previous scalar `c ^ d` by `c`. All reassociation and tensor-unit factors are
independent of the root. Exact comparison inverse image, tensoring with the
arbitrary input complex, intrinsic realization and its shift comparison preserve
natural-number scalar multiplication, yielding the displayed equality.
The argument includes `d = 0`, empty schemes, zero objects, and `c = 0` (the last
case can occur only at exponent one). No boundedness hypothesis is used. -/
theorem finiteReductionSourceTrivialization_power (P : PurityFiniteSetting.{u})
    (d c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionSourceTrivialization f d ζ' hζ' K).hom =
      c ^ d • (P.finiteReductionSourceTrivialization f d ζ hζ K).hom := by
  have hline : (P.finiteReductionShiftedLineChart X ζ' hζ').hom =
      c • (P.finiteReductionShiftedLineChart X ζ hζ).hom := by
    simp only [finiteReductionShiftedLineChart, Functor.mapIso_hom, Iso.symm_hom]
    rw [P.finiteReductionRootTrivialization_inv_power X c ζ ζ' hζ hζ' hc,
      Functor.map_nsmul, Functor.map_nsmul]
  have hetale : (P.finiteReductionEtalePowerTrivialization X ζ' hζ' d).hom =
      c ^ d • (P.finiteReductionEtalePowerTrivialization X ζ hζ d).hom := by
    unfold finiteReductionEtalePowerTrivialization finiteReductionEtaleRootPowerChart
      finiteReductionEtalePowerAssembly
    exact orderedPower_hom_nsmul _ _ _ _ _ _ _ _ _ _ c hline d
  have hpower : (P.finiteReductionPowerTrivialization X ζ' hζ' d).hom =
      c ^ d • (P.finiteReductionPowerTrivialization X ζ hζ d).hom := by
    simp only [finiteReductionPowerTrivialization, Iso.trans_hom, Functor.mapIso_hom]
    rw [hetale, Functor.map_nsmul, Preadditive.nsmul_comp]
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  have hfixed (ξ : P.field.k) (hξ : IsPrimitiveRoot ξ P.diagonalExponent) :
      P.finiteReductionFixedChart X d ξ hξ M =
        finiteReductionChartComposite P.Coefficient X M (P.diagonalTwist X d)
          (2 * (d : ℤ)) (P.finiteReductionPowerTrivialization X ξ hξ d ≪≫
            (shiftFunctor _ (2 * (d : ℤ))).mapIso
              (finiteReductionComparisonUnitChart P.Coefficient X)) :=
    eq_of_heq (P.existsUnique_finiteReductionFixedChart X d ξ hξ M).choose_spec.1
  have : ((smoothPurityTensor P.Coefficient X).obj M).Additive :=
    _root_.DerivedCategory.additive_tensorLeft M
  have hfixedPower : (P.finiteReductionFixedChart X d ζ' hζ' M).hom =
      c ^ d • (P.finiteReductionFixedChart X d ζ hζ M).hom := by
    rw [hfixed, hfixed]
    simp only [finiteReductionChartComposite, Iso.trans_hom, Functor.mapIso_hom]
    rw [hpower, Preadditive.nsmul_comp, Functor.map_nsmul]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  simp only [finiteReductionSourceTrivialization, Iso.trans_hom, Functor.mapIso_hom]
  rw [hfixedPower, Functor.map_nsmul, Preadditive.nsmul_comp]

end WeilConjectures.PurityFiniteSetting
