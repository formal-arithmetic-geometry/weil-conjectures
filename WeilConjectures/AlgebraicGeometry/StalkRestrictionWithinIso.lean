/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.StalkFromSpecSubopen

/-! # Stalk pullback after restriction inside a fixed open
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison for restriction inside an open and the fixed ambient stalk.

 Replace restriction by
pullback, compose pullbacks, and identify the composite scheme maps by cancelling
V.ι. This comparison applies to every module on V, independently of any complex. -/
noncomputable def stalkRestrictionWithinIso {Y : Scheme.{u}}
    (y : Y) (V : Y.Opens) (hyV : y ∈ V) (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    restrictFunctor (Y.homOfLE hUV) ⋙ pullback (U.fromSpecStalkOfMem y hyU) ≅
      pullback (V.fromSpecStalkOfMem y hyV) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback (Y.homOfLE hUV))
      (pullback (U.fromSpecStalkOfMem y hyU)) ≪≫
    pullbackComp (U.fromSpecStalkOfMem y hyU) (Y.homOfLE hUV) ≪≫
    pullbackCongr (Scheme.Opens.fromSpecStalkOfMem_homOfLE y V hyV U hUV hyU)

end AlgebraicGeometry.Scheme.Modules
