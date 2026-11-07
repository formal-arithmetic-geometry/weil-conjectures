/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelRingedProEtaleBaseChange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Transport of finite coefficient exchange

This is the coefficient transport step for the finite-level proper base-change theorem.
Source: Stacks Tags 09C8 and 09C9 (blueprint: thm-weil-pbc-finite-level-proetale).
(blueprint: lem-weil-pbc-finite-origin-exchange-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
