module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Trivial Kan fibrations

Source: Stacks Project, Simplicial, definition of trivial Kan fibrations, Tag 08NL
(blueprint: def-weil-pbc-trivial-kan-fibration).

The node's Mathlib match is `SSet.modelCategoryQuillen.I.rlp`: right lifting against every
boundary inclusion `∂Δ[n] ⟶ Δ[n]`, `n ≥ 0`. For `n = 0` the boundary is empty
(`SSet.boundary_zero`), and lifting against `∅ ⟶ Δ[0]` is surjectivity on vertices.
This name is a reducible alias of that Mathlib notion, so no second notion is introduced.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace SSet.Enhanced

/-- Surjectivity on vertices and lifting against every positive-dimensional boundary,
i.e. the right lifting property against all boundary inclusions `SSet.modelCategoryQuillen.I`.
Source: Stacks Project, Tag 08NL
(blueprint: def-weil-pbc-trivial-kan-fibration). -/
abbrev trivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop :=
  SSet.modelCategoryQuillen.I.rlp p

end SSet.Enhanced
