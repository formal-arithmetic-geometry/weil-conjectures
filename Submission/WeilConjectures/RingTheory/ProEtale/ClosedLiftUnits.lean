/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.RingTheory.ProEtale.ClosedLiftMap

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Units of the ind-etale closed lift

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`,
`lem-exc-closed-lift-units` (blueprint: lem-exc-closed-lift-units).
-/

@[expose] public section

universe u

namespace Algebra.ClosedLift

/-- An element of the closed lift is a unit if its image in the input algebra is a unit.
Source: blueprint `lem-exc-closed-lift-units`, statement and proof
(blueprint: lem-exc-closed-lift-units).

Proof: `isUnit_of_isUnit_image`, which lifts the inverse along a localization of a representing
étale stage of the colimit. -/
theorem isUnit_of_isUnit_toAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] (h : Algebra.ClosedLift A C)
    (hh : IsUnit (toAlgHom A C h)) : IsUnit h :=
  isUnit_of_isUnit_image A C h hh

end Algebra.ClosedLift
