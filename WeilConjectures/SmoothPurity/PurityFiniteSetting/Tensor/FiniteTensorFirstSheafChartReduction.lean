/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartFrameExt
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFirstSheafChartReductionFrameLift

/-! # Compatible first-root charts under coefficient reduction

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

/-- Compatible roots give the normalized coefficient-unit square in degree one.
Source: finite reduction of purity, Step 2; parent line-chart proof, Step 1;
Stacks 03PK and 03EK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction).
Proof: on an etale test object take the finite root section specified by ζ. The
root-tower projection is locally surjective on the pro-etale site, so lift this
section on a covering sieve to an infinite compatible root sequence. At level m
its projection is the section specified by η, because η is the prescribed power
of ζ. The normalized finite Tate site comparison identifies the finite root
pure tensor with the reduction of the common integral tensor. The degree-one
balancing clause of hc sends its A-reduction to its B-reduction. The two specified
first charts send these generators to coefficient one. The ordinary coefficient
unit sends one to one as well. Extend this equality by linearity and sheaf
separatedness, and use the section-normalized inverse realization/restriction
square to obtain the displayed equality in fixed-scalar coordinates. The
single/unit comparisons in the definition of the first chart are the localized
ordinary unit maps, so their inverse factors cancel. Equal levels and empty
schemes are covered by the same local calculation; no quotient flatness is used. -/
theorem finiteTensorFirstSheafChart_reduction
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    P.finiteTensorFixedLineMap m hm hmn T c 1 ≫
        (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)).map
          ((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).hom =
      (P.finiteTensorFirstSheafChart T ζ hζ).hom ≫
        Functor.LaxMonoidal.ε
          (sfFixedRestriction.{u, u + 1, u + 1} T
            (P.finiteReductionRingHom m hm hmn)) := by
  apply P.finiteTensorPositiveChart_frame_ext T
    (P.finiteTensorFirstSheafChart T ζ hζ) 1
    ((sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).obj
      (𝟙_ (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)))) _ _
  intro V b x₁ x hx₁ he₁ hx
  exact finiteTensorFirstSheafChart_reduction_frame_lift P m hm hmn T c hc ζ hζ η hη
    hroot V b x₁ x hx₁ he₁ hx
    (finiteTensorFirstSheafChart_reduction_unit_frame P m hm hmn T c hc ζ hζ η hη
      hroot V b x₁ hx₁ he₁)

end WeilConjectures.PurityFiniteSetting
