/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.ReductionCoefficients

public import WeilConjectures.WeilSheaf.Strategy3.Coefficient

public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficientsComp
public import WeilConjectures.TateTwist.IntegralReduction

/-! # Independent coefficient/pullback infrastructure: IntegralReduction -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] (n : ℕ)
  {k : Type u} [Field k] {X : Scheme.{u}}


variable [NeZero (ℓ : k)]

noncomputable def extendScalarsIntegralTateTwistOneIntegersModPowIso (f : X ⟶ Spec (.of k)) :
    (Mod.extendScalars (integersModPowReduction ℓ E n X)).obj (integralTateTwistOne X ℓ E) ≅
      (Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl.integersModPow ℓ E n)) X)).obj
        (rootsOfUnitySheaf X (ℓ ^ n)) :=
  (Mod.extendScalarsCompIsoOfEq (coefficientMap_comp_eq _ _ _ rfl X)).app (tateModule X ℓ) ≪≫
    extendScalarsTateModuleIso f ℓ (compositeReduction ℓ E n) n
      (Profinite.natCast_pow_zsmul_id_integersModPowRingObj_eq_zero ℓ E n)


end AlgebraicGeometry.ProEtale.Strategy3
