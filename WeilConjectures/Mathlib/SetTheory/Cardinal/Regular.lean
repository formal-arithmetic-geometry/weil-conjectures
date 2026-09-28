/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# The well-order attached to a regular cardinal

For a regular cardinal `κ`, the well-ordered type `κ.ord.ToType` is nonempty and has no
maximal element. We register the resulting `OrderBot` and `NoMaxOrder` structures as
instances, so that transfinite constructions indexed by `κ.ord.ToType` can be stated
without carrying them as hypotheses.

-/

@[expose] public section

universe u

namespace Cardinal

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The least element of `κ.ord.ToType` for a regular cardinal `κ`. -/
noncomputable instance orderBotOrdToTypeOfIsRegular : OrderBot κ.ord.ToType :=
  have : Nonempty κ.ord.ToType := by
    simpa using (Fact.out : κ.IsRegular).ne_zero
  WellFoundedLT.toOrderBot _

/-- For a regular cardinal `κ`, the well-order `κ.ord.ToType` has no maximal element. -/
instance noMaxOrderOrdToTypeOfIsRegular : NoMaxOrder κ.ord.ToType :=
  Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le

end Cardinal
