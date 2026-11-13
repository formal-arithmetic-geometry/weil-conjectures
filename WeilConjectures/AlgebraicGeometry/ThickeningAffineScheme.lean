/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-!
# Affineness of a thickening

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A thickening of an affine scheme is affine.
-/
theorem isAffine_of_isThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsThickening i) [IsAffine X] : IsAffine X' := by
  let : IsClosedImmersion i := hi.1
  let : Surjective i := hi.2
  exact isAffine_of_surjective_of_universallyClosed i

end AlgebraicGeometry
