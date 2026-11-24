/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackCompositionPointwise

/-! Composition law for pullback on structure-sheaf cohomology.

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tags 01F7, 01FB
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback on structure-sheaf cohomology reverses composition. -/
theorem structureSheafCohomologyPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    structureSheafCohomologyPullback (f ≫ g) n =
      (structureSheafCohomologyPullback f n).comp
        (structureSheafCohomologyPullback g n) := by
  ext x
  exact structureSheafCohomologyPullback_comp_apply f g n x

end AlgebraicGeometry.Scheme
