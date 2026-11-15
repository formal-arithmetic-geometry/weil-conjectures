/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback

import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullbackIdentity
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackComposition

/-!
# Functoriality of pullback on structure sheaf cohomology

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tag 01F7
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Canonical pullback on structure sheaf cohomology preserves identities and reverses
composition. -/
theorem structureSheafCohomologyPullback_functorial :
    (∀ (X : Scheme.{u}) (n : ℕ),
      structureSheafCohomologyPullback (𝟙 X) n =
        AddMonoidHom.id (Sheaf.H (structureSheafAb X) n)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ),
      structureSheafCohomologyPullback (f ≫ g) n =
        (structureSheafCohomologyPullback f n).comp
          (structureSheafCohomologyPullback g n)) := by
  constructor
  · intro X n
    exact structureSheafCohomologyPullback_identity X n
  · intro X Y Z f g n
    exact structureSheafCohomologyPullback_comp f g n

end AlgebraicGeometry.Scheme
