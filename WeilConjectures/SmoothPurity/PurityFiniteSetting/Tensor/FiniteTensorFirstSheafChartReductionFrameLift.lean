/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFirstSheafChartReductionUnitFrame

import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! Extension of the local unit-frame calculation to an arbitrary frame section. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/--
If the coefficient-reduction first-chart square holds on one unit-frame
generator, it holds on every section representing the same frame basis vector.
Proof: the section map `finiteTensorSection` is the intrinsic section
equivalence of the realization (Stacks 03EK), hence injective; two sections
with the same image `b.basis 1 0` are equal, and the hypothesis is the claim.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-frame-lift)
-/
theorem finiteTensorFirstSheafChart_reduction_frame_lift
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
    (x : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (hx₁ : HEq (P.finiteTensorSection T 1 V x₁)
      (P.finiteTensorFrameBasis T V b 1))
    (he₁ : (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient))
    (hx : HEq (P.finiteTensorSection T 1 V x)
      (P.finiteTensorFrameBasis T V b 1))
    (hbase :
      (P.finiteTensorFixedLineMap m hm hmn T c 1 ≫
          (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).map
            ((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).hom).hom.app
              (Opposite.op V) x₁ =
        ((P.finiteTensorFirstSheafChart T ζ hζ).hom ≫
          Functor.LaxMonoidal.ε
            (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn))).hom.app
              (Opposite.op V) x₁) :
    (P.finiteTensorFixedLineMap m hm hmn T c 1 ≫
        (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).map
          ((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).hom).hom.app
            (Opposite.op V) x =
      ((P.finiteTensorFirstSheafChart T ζ hζ).hom ≫
        Functor.LaxMonoidal.ε
          (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn))).hom.app
            (Opposite.op V) x := by
  have hs : P.finiteTensorSection T 1 V x = P.finiteTensorSection T 1 V x₁ :=
    eq_of_heq (hx.trans hx₁.symm)
  have hxx : x = x₁ := by
    let : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    exact (sfIntrinsicSectionEquiv P.Ring T (P.finiteTensorLine T 1)
      (Opposite.op V)).injective hs
  subst hxx
  exact hbase

end WeilConjectures.PurityFiniteSetting
