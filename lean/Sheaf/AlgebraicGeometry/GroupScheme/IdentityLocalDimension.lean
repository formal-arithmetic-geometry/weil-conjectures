/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic
import Sheaf.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.RingTheory.ClosedPointDimensionLocalRing
import Sheaf.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

/-!
# The dimension of a finite type group scheme at the identity

Source: blueprint `sk-i-cartier`, third proof paragraph, and the dimension paragraph of
`lem-wf-same-lie-closed-subgroup`.
(blueprint: lem-ag-group-identity-local-dimension)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- The local ring at the identity of a finite type group scheme has its global dimension.

Source: blueprint `sk-i-cartier`, third proof paragraph, and
`lem-wf-same-lie-closed-subgroup`, the dimension paragraph.
(blueprint: lem-ag-group-identity-local-dimension)

Proof: First extend the base field to its algebraic closure. For finite type schemes global
Krull dimension is unchanged by algebraic field extension. The local dimension at a rational
point is also unchanged: in an affine neighbourhood the extension is integral and faithfully
flat, and the local map at the lifted rational point has zero-dimensional fibre, so the
local dimensions agree. Over the algebraic closure every closed point is rational, by the
Nullstellensatz. Left translation by its value is an automorphism carrying the identity to
that point, so it induces an isomorphism of local rings. Every closed point consequently has
the same local dimension as the identity. A finite type scheme over a field is Noetherian;
its dimension is the supremum of the local dimensions at closed points (each point specializes
to a closed point and local dimension is nondecreasing under specialization). This supremum
is the common value, since the identity supplies a closed point. Descend the two dimensions
back to the original field. This argument uses neither smoothness nor characteristic zero,
and nilpotents do not affect any of the dimensions. -/
theorem localKrullDim_identity_eq_topologicalKrullDim
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ringKrullDim (G.left.presheaf.stalk
      (unitSection G (IsLocalRing.closedPoint k))) = topologicalKrullDim G.left := by sorry

end AlgebraicGeometry.GrpObj
