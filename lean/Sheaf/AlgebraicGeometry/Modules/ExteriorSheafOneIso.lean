module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The first exterior sheaf is canonically isomorphic to the original sheaf.
Source: Stacks Project, Tag 0BRT, degree-one specialization; Mathlib
`exteriorPower.oneEquiv` and the sheafification adjunction.
(blueprint: lem-sc-smooth-proper-curve-dualizing-exterior-one)
Proof: on each open U, use `exteriorPower.oneEquiv` to send the singleton wedge of
m to m. For a restriction U to V, the chosen exterior restriction sends the singleton
wedge of m to the singleton wedge of its restriction, by
`exteriorSheafRestriction_existsUnique`. Thus the degree-one equivalences commute with
restrictions on singleton wedges, and on every element because these wedges span.
Their inverses also commute with restrictions, giving an isomorphism from
`exteriorSheafPresheaf M 1` to `M.val`. Apply the sheafification functor to this
isomorphism, then compose with the invertible counit of
`PresheafOfModules.sheafificationAdjunction` at M. Since M is already a sheaf, this
counit identifies the sheafification of `M.val` with M, proving the result.
-/
theorem exteriorSheaf_one_iso {X : Scheme.{u}} (M : X.Modules) :
    Nonempty (exteriorSheaf M 1 ≅ M) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
