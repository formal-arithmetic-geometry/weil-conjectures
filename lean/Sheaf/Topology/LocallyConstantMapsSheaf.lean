import Sheaf.Topology.LocallyConstantMapsPresheaf
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Locally constant maps form a sheaf

Source: Stacks Project, Sheaves, Example 6.4 and Definition 6.5 (Tag 006W)
(blueprint: lem-weil-pbc-locally-constant-maps-sheaf).
-/

set_option autoImplicit false

universe w z

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Locally constant maps into a set satisfy the sheaf condition on opens.

Source: Stacks Project, Sheaves, Example 6.4 and Definition 6.5 (Tag 006W).
(blueprint: lem-weil-pbc-locally-constant-maps-sheaf).
Proof: for a covering of an open by opens, compatible sections glue pointwise.
The glued map is locally constant because each point lies in a covering member,
and uniqueness is pointwise. -/
theorem locallyConstantMapsPresheaf_isSheaf (X : TopCat.{w}) (R : Type z) :
    Presheaf.IsSheaf (locallyConstantMapsPresheaf X R) := by
  sorry

end TopCat
