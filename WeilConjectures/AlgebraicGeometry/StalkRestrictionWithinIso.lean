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

For `y ∈ U ≤ V`, restricting a module on `V` to `U` and pulling back to the stalk spectrum
at `y` is canonically isomorphic to pulling back directly from `V`.

## Implementation details

The comparison replaces restriction by pullback, composes pullbacks, and identifies the
composite scheme maps using `Scheme.Opens.fromSpecStalkOfMem_homOfLE`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison for restriction inside an open and the fixed ambient stalk:
restriction along `U ≤ V` followed by pullback along `U.fromSpecStalkOfMem y hyU` is
isomorphic to pullback along `V.fromSpecStalkOfMem y hyV`. -/
noncomputable def stalkRestrictionWithinIso {Y : Scheme.{u}}
    (y : Y) (V : Y.Opens) (hyV : y ∈ V) (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    restrictFunctor (Y.homOfLE hUV) ⋙ pullback (U.fromSpecStalkOfMem y hyU) ≅
      pullback (V.fromSpecStalkOfMem y hyV) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback (Y.homOfLE hUV))
      (pullback (U.fromSpecStalkOfMem y hyU)) ≪≫
    pullbackComp (U.fromSpecStalkOfMem y hyU) (Y.homOfLE hUV) ≪≫
    pullbackCongr (Scheme.Opens.fromSpecStalkOfMem_homOfLE y V hyV U hUV hyU)

end AlgebraicGeometry.Scheme.Modules
