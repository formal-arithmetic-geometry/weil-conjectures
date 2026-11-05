/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Tower
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTatePullback

/-! # Independent coefficient/pullback infrastructure: IntegralPullback -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X) (f : X ⟶ Spec (.of k))

/-- Pullback of the integral Tate line, using the canonical root-of-unity comparisons
at every level of its defining tower. -/
noncomputable def upperStarIntegralTateTwistOneIso :
    (Strategy3.upperStar (Profinite.padicIntegersRingObj ℓ E) g).obj
      (integralTateTwistOne X ℓ E) ≅ integralTateTwistOne X' ℓ E :=
  upperStarExtendScalarsLimitFreeTowerIso (Profinite.continuousMapRingObj ℤ_[ℓ]) g
    (F := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (F' := fun n ↦ rootsOfUnitySheaf X' (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X' (ℓ ^ n) ℓ)
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ n))
    (Profinite.padicIntRingObjToPadicIntegers ℓ E)
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (preservesLimit_upperStar_tateModuleSystem ℓ g f)


end AlgebraicGeometry.ProEtale.Strategy3
