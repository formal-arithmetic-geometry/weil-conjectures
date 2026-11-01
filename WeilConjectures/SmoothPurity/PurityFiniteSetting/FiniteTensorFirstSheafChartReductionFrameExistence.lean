/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- A normalized line map sends a source frame generator to a reduced frame generator.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame-frame)
Proof: by the degree-one balancing clause of `hc`, `c 1` is the coefficient
reduction `L ⊗ R_n → L ⊗ R_m` on local pure tensors, hence everywhere by sheaf
separatedness; the reduction of a local generator of the invertible line is a
generator. Its tensor powers and dual evaluations are generators of the reduced
signed powers, so the ordered signed-line frame construction gives a reduced frame
whose degree-one basis vector is `c 1 (b.basis 1 0)`. -/
theorem finiteTensorFirstSheafChart_reduction_frame_exists
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (V : T.ProEt) (b : P.FiniteTensorFrame T V) :
    ∃ bB : (P.finiteReductionSetting m hm).FiniteTensorFrame T V,
      P.finiteTensorLineSectionMap m hm hmn T c 1 (Opposite.op V)
          (P.finiteTensorFrameBasis T V b 1) =
        (P.finiteReductionSetting m hm).finiteTensorFrameBasis T V bB 1 := by
  sorry
end WeilConjectures.PurityFiniteSetting
