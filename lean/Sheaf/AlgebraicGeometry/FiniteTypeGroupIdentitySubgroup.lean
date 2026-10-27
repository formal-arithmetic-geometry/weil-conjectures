/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion

/-!
# The identity component of a finite-type group scheme

Source: Stacks Project, `groupoids.tex`, Tag 0B7R, `proposition-connected-component`;
Milne, Algebraic Groups (2017), Proposition 1.34, pp. 16-17
(blueprint: lem-sfb-finite-type-group-identity-subgroup).

The canonical open subscheme `GrpObj.identityComponent G` and its restricted group
structure are those of `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over an arbitrary field, the identity component of a finite-type group scheme is
clopen, connected with its open-subscheme structure, and a closed subgroup scheme.
The group structure and inclusion are the canonical restrictions to that open subscheme.

Source: Stacks Project, `groupoids.tex`, Tag 0B7R, `proposition-connected-component`;
Milne, Algebraic Groups (2017), Proposition 1.34, pp. 16-17
(blueprint: lem-sfb-finite-type-group-identity-subgroup).

Proof:
1. By lem-trf-finite-type-component-open-qc, the component C of the identity is open
and its open subscheme H is nonempty and connected.
2. The closure of a connected set is connected: a separation of the closure restricts
to one of the dense connected set. Maximality gives closure C = C. Similarly, the
continuous image of a connected set is connected, and every connected subset containing
the identity lies in C, since its union with C is connected (def-weil-connected-scheme).
3. The unit section factors uniquely through H by
lem-weil-pbc-morphism-factors-through-open-subscheme. Its geometrically connected source
Spec k and connected target H give geometric connectedness of H by
lem-trf-geometrically-connected-image-criterion.
4. By lem-weil-pbc-geometrically-connected-product-components, H times H is connected.
Its image under the restricted multiplication is connected and contains the identity,
so lies in C. Factor multiplication through H using the open-subscheme factorization.
5. Inversion fixes the identity and sends H to a connected subset containing it; hence
it too factors uniquely through H (def-sc-group-scheme and the same factorization lemma).
6. Factorization uniqueness makes the inclusion j a monomorphism. Compose the
associativity, unit and inverse diagrams with j, use the diagrams of G, and cancel j.
These give the restricted group structure, and j respects multiplication.
7. The open immersion j is an immersion with closed image C. Apply
lem-weil-pbc-immersion-closed-image-closed-immersion. On every k-algebra's points j is
injective by monicity and preserves the group operations by their factorizations, so
it is a closed subgroup scheme in the sense of def-sc-group-scheme-subgroup.
-/
theorem GrpObj.finiteType_identityComponent_closedSubgroup
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsClopen (connectedComponent (GrpObj.onePoint G)) ∧
      ConnectedSpace (GrpObj.identityComponent G).left ∧
      IsClosedSubgroupScheme (GrpObj.identityComponentι G) := by
  sorry

end AlgebraicGeometry
