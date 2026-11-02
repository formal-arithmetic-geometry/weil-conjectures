/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Integral connected components from domain stalks

Source: Stacks Project, Properties, Tag 033N and the following remark, with the
weaker domain-stalk hypothesis supplied by the proved source-library theorem
`irreducibleSpace_of_isDomain_stalk`
(blueprint: lem-wrp-locnoeth-domain-stalk-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The connected components of a locally Noetherian scheme with domain stalks are
clopen and integral with their open subscheme structures.

Source: Stacks Project, Properties, Tag 033N and remark-normal-connected-irreducible;
proved source-library tools in `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`
(blueprint: lem-wrp-locnoeth-domain-stalk-components).

Proof:
1. A locally Noetherian scheme has Noetherian affine neighbourhoods. Such spaces are
   locally connected, so every connected component is open; components are always closed.
2. Give the component its open subscheme structure. It is nonempty and connected,
   remains locally Noetherian, and its stalks are isomorphic to the ambient domain stalks.
3. Apply the proved source theorem `irreducibleSpace_of_isDomain_stalk` to this component:
   its domain stalks ensure that each point has an irreducible open neighbourhood;
   connectedness then forces the whole component to be irreducible.
4. Domain stalks are reduced, so the component scheme is reduced. A nonempty irreducible
   reduced scheme is integral. The empty ambient scheme has no points to check.
-/
theorem locally_noetherian_domain_stalk_components
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (y : X) :
    IsClopen (connectedComponent y) ∧
      ∃ U : X.Opens, (U : Set X) = connectedComponent y ∧ IsIntegral U.toScheme := by
  classical
  have hcl : IsClopen (connectedComponent y) := isClopen_connectedComponent
  let U : X.Opens := ⟨connectedComponent y, hcl.isOpen⟩
  have : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hdom (z : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk z) := by
    have := hX (U.ι z)
    let e := (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
    exact e.symm.injective.isDomain e.symm.toRingHom
  have : IrreducibleSpace U.toScheme := irreducibleSpace_of_isDomain_stalk _ hdom
  have : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact ⟨hcl, U, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end AlgebraicGeometry
