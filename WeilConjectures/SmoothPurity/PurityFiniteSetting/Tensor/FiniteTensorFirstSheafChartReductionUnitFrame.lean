/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts

/-! Local unit-frame calculation for the compatible first-root chart. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/--
On a chosen pro-etale frame generator, compatible primitive roots identify the
coefficient-reduction first-chart square in degree one.  The proof lifts the
root section through the root tower, applies the normalized Tate comparison,
and then uses the degree-one balancing and chart normalizations.  It finishes
by transporting the local equality through the inverse realization/restriction
square.  This is the local calculation required by
`lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame`.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame)
-/
theorem finiteTensorFirstSheafChart_reduction_unit_frame
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m)))
    (V : T.ProEt) (b : P.FiniteTensorFrame T V)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (hx₁ : HEq (P.finiteTensorSection T 1 V x₁)
      (P.finiteTensorFrameBasis T V b 1))
    (he₁ : (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :
    (P.finiteTensorFixedLineMap m hm hmn T c 1 ≫
        (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).map
          ((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).hom).hom.app
            (Opposite.op V) x₁ =
      ((P.finiteTensorFirstSheafChart T ζ hζ).hom ≫
        Functor.LaxMonoidal.ε
          (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn))).hom.app
            (Opposite.op V) x₁ := by
  sorry

end WeilConjectures.PurityFiniteSetting
