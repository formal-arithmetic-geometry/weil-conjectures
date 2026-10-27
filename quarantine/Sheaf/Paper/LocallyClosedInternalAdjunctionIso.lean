/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.InternalAdjunctionPairingChange

/-! # Invertibility of the specified locally closed internal adjunction

Source: blueprint thm-coef-finite-hom, paragraph 3, internal stratum adjunction
(blueprint: lem-coef-locally-closed-internal-adjunction-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

/-- The evaluation-defined internal adjunction is invertible without a Tor bound.
Source: thm-coef-finite-hom, paragraph 3, internal stratum adjunction
(blueprint: lem-coef-locally-closed-internal-adjunction-iso).

Proof: For fixed L the closed proper projection map followed by the inverse open
projection is a natural isomorphism from tensoring with g_*j_!L to the composite
of g-star, j-star, tensoring with L and g_*j_!. The closed factor is invertible by
the finite-ring proper projection theorem; the open factor is the published open
projection isomorphism. Compose the two ordinary pullback/direct-image adjunctions,
the tensor-Hom adjunction and the compact-support exceptional adjunction. Conjugate
the projection isomorphism along this composite and the tensor-Hom adjunction on X.
Conjugation preserves isomorphisms. Its counit equation says that the component at
M is the transpose of projection followed by compact direct image of the ordinary
counit and evaluation, followed by the exceptional counit. Expanding the composite
counits gives precisely internalAdjunction as defined, so its component is an
isomorphism. No constructibility, nonemptiness or boundedness assumption occurs. -/
theorem locallyClosedInternalAdjunction_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    IsIso (internalAdjunction A g j L M) := by
  sorry

end AlgebraicGeometry.Etale
