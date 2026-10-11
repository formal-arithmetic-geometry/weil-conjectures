import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.AssociatedPoints

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Schemes without embedded points

Source: Stacks Project, Divisors, Tag 02OZ (blueprint: def-sc-no-embedded-points).
-/

/-- A scheme has no embedded points when every associated point of its structure sheaf is
one of the generic points of an irreducible component.
Source: Stacks Project, Divisors, Tag 02OZ (blueprint: def-sc-no-embedded-points). -/
class NoEmbeddedPoints (X : Scheme.{u}) : Prop where
  associatedPoints_are_generic : ∀ x : X, x ∈ associatedPoints X → x ∈ genericPoints X

end AlgebraicGeometry
