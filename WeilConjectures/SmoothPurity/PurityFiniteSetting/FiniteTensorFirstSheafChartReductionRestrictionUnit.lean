/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Scalar restriction sends the ordinary coefficient unit to the reduced unit.
Source: Stacks 00YV and finite reduction Step 2.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame-restriction)
This is the lax monoidal unit naturality equation for `sfFixedRestriction`,
proved by evaluating the sheafification unit on `1`. -/
theorem finiteTensorFirstSheafChart_reduction_restriction_unit
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) (V : T.ProEt) :
    (Functor.LaxMonoidal.ε (sfFixedRestriction T
      (P.finiteReductionRingHom m hm hmn))).hom.app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V)
            (1 : P.Coefficient)) =
      (P.finiteReductionSetting m hm).finiteTensorUnitSection T V := by
  have h := ConcreteCategory.congr_hom
    (congr_app (CategoryTheory.Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose
      (ProEt.topology T)
      (ModuleCat.restrictScalars.{u + 1}
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}))
        (Opposite.op V)) (1 : P.Coefficient)
  change (Functor.LaxMonoidal.ε (sfFixedRestriction T
      (P.finiteReductionRingHom m hm hmn))).hom.app (Opposite.op V)
        (P.finiteTensorUnitSection T V) =
    (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient))).app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (ModuleCat.restrictScalars.{u + 1}
          (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}))
            (1 : P.Coefficient)) at h
  simpa only [ModuleCat.restrictScalars_η, map_one, finiteTensorUnitSection] using h
end WeilConjectures.PurityFiniteSetting
