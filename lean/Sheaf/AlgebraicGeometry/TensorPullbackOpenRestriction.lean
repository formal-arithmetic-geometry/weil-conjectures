/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Unit-compatible restriction and tensor pullback for open immersions

Source: Stacks Project, Sheaves, Tags 0095, 0096 and 0097
(blueprint: lem-weil-pbc-open-immersion-module-pullback-restriction).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction agrees with the recorded tensor pullback, naturally in the module.
This is the unique left-adjoint comparison compatible with the two units.
Source: Stacks, Tags 0095 and 0096
(blueprint: lem-weil-pbc-open-immersion-module-pullback-restriction). -/
noncomputable def restrictFunctorIsoTensorPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : restrictFunctor f ≅ tensorPullback f :=
  (restrictAdjunction f).leftAdjointUniq
    (Classical.choose (exists_tensorPullbackAdjunction f))

/-- The comparison sends the ordinary restriction unit to the canonical tensor unit.
Its evaluation on an open W and a section m is the equation in the node, since the
restriction unit is the ordinary restriction map (`restrictAdjunction_unit_app_app`).
Source: Stacks, Tags 0095 and 0096
(blueprint: lem-weil-pbc-open-immersion-module-pullback-restriction).
Proof: restriction along an open immersion is left adjoint to pushforward, with
unit the restriction map. The tensor pullback is left adjoint to that same
pushforward by lem-pc-module-pullback-adjunction. The unique left-adjoint
comparison is an isomorphism and is natural in the module. Its unit equation is
CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app. Evaluate this equality
on every open W to obtain the sectionwise formula, including the empty open. -/
theorem restrictFunctorIsoTensorPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    (restrictAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoTensorPullback f).hom.app M) =
      (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M := by
  sorry

end AlgebraicGeometry.Scheme.Modules
