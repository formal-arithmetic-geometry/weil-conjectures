/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module



public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence

/-! # Existence of the canonical strict-local neighbourhood geometry

Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The pullback of the strict henselization is the limit of the small affine
neighbourhood pullbacks, with qcqs stages and affine transition morphisms.
This supplies only geometry, with no derived sheaves, cocones or mates.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: lem-weil-pbc-strict-local-neighbourhood-geometry).

Proof: apply the proved upstream existence theorem
`nonempty_strictLocalNeighbourhoodGeometry`, which states exactly this for the same
structure. Consumers that need the cone on the original coordinate-ring colimit model
use the `smallModelLegs`, `smallModelIsLimit`, `smallModelFirst` and `smallModelOver` API
of StrictLocalSmallModel.NeighbourhoodGeometry. -/
theorem smallModel_nonempty_strictLocalNeighbourhoodGeometry {X S : Scheme.{v}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Nonempty (StrictLocalNeighbourhoodGeometry f s) := by
  exact nonempty_strictLocalNeighbourhoodGeometry f s

end AlgebraicGeometry.Etale
