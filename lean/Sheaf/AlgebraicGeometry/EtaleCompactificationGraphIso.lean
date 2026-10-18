/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap

/-!
# Invertibility of graph extension for an etale compactification

Source: Stacks Project, Etale Cohomology, Tag 0F4L, and More on Etale Cohomology,
Tags 0F4Y (lemma-separated-etale-shriek) and 0F52 (lemma-compactify-f-shriek-separated).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical graph extension identifies etale sum extension with proper pushforward
of open extension in a compactification.

Source: Stacks Project, Etale Cohomology, Tag 0F4L, graph construction; More on Etale
Cohomology, Tags 0F4Y and 0F52 (lemma-compactify-f-shriek-separated).
(blueprint: lem-f7-etale-compactification-graph-iso).

Proof: The graph used in the definition is clopen: it is open as the composite of an
etale diagonal with the base change of the open immersion, and closed as a section of
the proper projection. Its projection on sheaves is identity on this component and
zero on its complement. Pulling this decomposition back along any change of base gives
the corresponding graph projection. The etale sum base-change isomorphism and ordinary
inverse-image/direct-image exchange are mates of the same restriction identity; their
pasting and the graph projection therefore make the graph-extension map commute with
base change. The existing open-extension API
`openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap` supplies the compatibility
with ordinary exchange on the open-extension component. In particular proper base
change in degree zero identifies its pullback
to a geometric point with the graph-extension map on the geometric fibre.
The fibre of the quasi-compact etale morphism is a finite disjoint union of spectra of
algebraically closed fields. It is an open and closed subscheme of the proper fibre:
its finitely many points are closed, since they have residue field equal to the base
field. The graph-extension map is consequently the canonical map from the finite sum
of the sheaf stalks to their finite product. On each summand its graph projection is
the identity on that point and zero at every other point. The sum-to-product map is an
isomorphism, including for the empty fibre. Exact conservative geometric stalks detect
isomorphisms, so the original graph extension is an isomorphism for every sheaf.
All component maps are linear. The clopen-product calculation can be made after
forgetting the module structure, and the forgetful functor reflects isomorphisms.
All maps are natural in that sheaf by construction, giving the functor isomorphism.
The argument uses no Noetherian assumption on the original schemes. -/
theorem isIso_etaleCompactificationGraphMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (c : Compactification u) : IsIso (etaleCompactificationGraphMap A u c) := by
  sorry

end AlgebraicGeometry.Etale
