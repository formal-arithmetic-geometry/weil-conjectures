/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFirstSheafChartReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorChartRecursionReduction

/-! # Compatible root charts of ordinary finite coefficient lines

Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

private theorem charts_eq_recursion (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteTensorSheafCharts T ζ hζ =
      P.finiteTensorOrdinaryChartRecursion T (P.finiteTensorFirstSheafChart T ζ hζ) := by
  apply (P.existsUnique_finiteTensorSheafCharts T ζ hζ).unique
  · exact (P.existsUnique_finiteTensorSheafCharts T ζ hζ).exists.choose_spec
  · intro d V b x₁ x hx₁ he₁ hx
    exact P.finiteTensorOrdinaryChartRecursion_normalized T
      (P.finiteTensorFirstSheafChart T ζ hζ) d V b x₁ x hx₁ he₁ hx

/-- Ordinary normalized semilinear reduction commutes with compatible root charts.
Source: finite reduction of purity, Step 2; the parent line-chart proof, Steps 1--2;
Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-sheaf-chart-reduction).
Proof: locally lift the primitive root at level n to a compatible infinite root
sequence. Its level-m projection is the specified root by the power relation.
The normalized first-site comparison identifies the integral generator's image
with the corresponding root generator. The degree-one balancing equation for c
therefore sends the first A-generator to the first B-generator. The positive
recursion for c sends their ordered tensor powers to one another. The sheaf
charts send those generators to the unit sections, and the lax unit of scalar
restriction sends coefficient one to coefficient one. At degree zero use the
coefficient-map clause of c's normalization. Linearity gives equality on all local
sections; sheaf separatedness glues the equality, and the normalized inverse
realization/restriction square gives the displayed fixed-scalar equation. Changes
of integral lift fix the finite generators at both levels. Equal levels, empty
schemes and ramified quotients require no modification or flatness assumption. -/
theorem finiteTensorSheafChart_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    P.finiteTensorFixedLineMap m hm hmn T c d ≫
      (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).map
        ((P.finiteReductionSetting m hm).finiteTensorSheafCharts T η hη d).hom =
    (P.finiteTensorSheafCharts T ζ hζ d).hom ≫
      Functor.LaxMonoidal.ε
        (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)) := by
  rw [charts_eq_recursion P T ζ hζ,
    charts_eq_recursion (P.finiteReductionSetting m hm) T η hη]
  exact P.finiteTensorChartRecursion_reduction m hm hmn T c hc _ _
    (P.finiteTensorFirstSheafChart_reduction m hm hmn T c hc ζ hζ η hη hroot) d

end WeilConjectures.PurityFiniteSetting
