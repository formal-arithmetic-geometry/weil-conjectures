/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Limits

/-!
# The forgetful functor from rings reflects limits of arbitrary size

Mathlib provides `RingCat.forget_preservesLimitsOfSize` only under the hypothesis
`UnivLE.{v, u}`, which is too restrictive to check sheaf conditions for `RingCat`-valued
presheaves on the (large) site of schemes: there the relevant diagrams are indexed by a
category one universe up. The corresponding statement for `AddCommGrpCat` is available
unconditionally (`AddCommGrpCat.forget_createsLimitsOfSize`), which is why
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb` goes through in Mathlib.

The instance below is the missing ring-valued analogue. It is used exactly once, to
transfer the sheaf condition for `AlgebraicGeometry.continuousMapPresheaf` to the presheaf
of rings `U ↦ C(U, R)`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

/-- The forgetful functor from rings to types reflects limits of arbitrary size.

TODO: this should be upstreamed to Mathlib, by relaxing the `UnivLE` hypothesis on
`RingCat.forget_preservesLimitsOfSize` in the same way as for `AddCommGrpCat`. -/
instance RingCat.forget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{w, v} (forget RingCat.{u}) := sorry
