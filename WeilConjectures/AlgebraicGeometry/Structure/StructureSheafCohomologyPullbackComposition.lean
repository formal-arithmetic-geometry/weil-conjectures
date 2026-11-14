/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackCompositionPointwise

/-! Composition law for pullback on structure-sheaf cohomology.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback on structure-sheaf cohomology reverses composition.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7 and Remark 01FB. -/
theorem structureSheafCohomologyPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    structureSheafCohomologyPullback (f ≫ g) n =
      (structureSheafCohomologyPullback f n).comp
        (structureSheafCohomologyPullback g n) := by
  ext x
  exact structureSheafCohomologyPullback_comp_apply f g n x

end AlgebraicGeometry.Scheme
