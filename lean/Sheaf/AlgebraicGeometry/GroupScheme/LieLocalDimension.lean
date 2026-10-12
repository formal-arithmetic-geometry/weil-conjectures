/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.RingTheory.SmoothOverFieldRegularLocal

/-!
# Lie dimension and the local ring at a smooth identity

Source: blueprint `sk-i-cartier`, third proof paragraph, and the dimension paragraph of
`lem-wf-same-lie-closed-subgroup`.
(blueprint: lem-ag-smooth-lie-local-dimension)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- The Lie algebra of a smooth group scheme has the dimension of its local ring at the identity.

Source: blueprint `sk-i-cartier`, third proof paragraph, and
`lem-wf-same-lie-closed-subgroup`, the dimension paragraph.
(blueprint: lem-ag-smooth-lie-local-dimension)

Proof: Write `e` for the image of the unique point of `Spec k` under the identity section.
The section identifies the residue field at `e` with `k`. Restrict to an affine neighbourhood
of `e`. Its algebra is smooth over `k`, so the local ring `R` at `e` is Noetherian and regular.
The fibre of relative differentials at this rational point is canonically the cotangent space
`m/m²`: the conormal exact sequence is split by the structural map from `k`, and the
induced derivation on `R` gives the inverse identification. Pulling the cotangent sheaf back
along the identity section therefore gives the sheaf associated to `m/m²` on `Spec k`.
Morphisms from it to the structure sheaf identify, linearly over `k` via the global-sections
isomorphism of `Spec k`, with the dual of `m/m²`. This is exactly the definition of `Lie G`.
The cotangent space is finite dimensional, its dual has the same finrank, and regularity
identifies that finrank with the Krull dimension of `R`. -/
theorem finrank_lie_eq_localKrullDim_of_smooth
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) =
      ringKrullDim (G.left.presheaf.stalk
        (unitSection G (IsLocalRing.closedPoint k))) := by sorry

end AlgebraicGeometry.GrpObj
