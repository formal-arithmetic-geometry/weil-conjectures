/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The existence part of the valuative criterion is local at the target

Mathlib identifies `AlgebraicGeometry.ValuativeCriterion.Existence` with the universal
version of `SpecializingMap`, which is local at the target; we record the resulting
`IsZariskiLocalAtTarget` instance.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

instance : IsZariskiLocalAtTarget ValuativeCriterion.Existence := by
  rw [ValuativeCriterion.Existence.eq]
  refine universally_isZariskiLocalAtTarget _ ?_
  intro X Y f ι U hU H
  exact IsZariskiLocalAtTarget.of_iSup_eq_top U hU H

end AlgebraicGeometry
