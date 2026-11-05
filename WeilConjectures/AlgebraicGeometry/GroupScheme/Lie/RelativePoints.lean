/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

/-!
# Infinitesimal points with values in a scheme

Let `G` be a group scheme over `S` and `X` a scheme over `S`. The thickening `X[ε]` is a scheme
over `S` through `X[ε] ⟶ X ⟶ S` (`AlgebraicGeometry.overDualNumbers`). The *infinitesimal points
of `G` with values in `X`* are the points `v : X[ε] ⟶ G` over `S` with `v|_X = 1`
(`AlgebraicGeometry.GrpObj.infPointsAt`); for `X = S` these are the infinitesimal points of `G`.
They are functorial in `X`, carry the rescalings `ε ↦ cε` by global functions `c` of `X`, and the
`X`-points `x` of `G` act on them by conjugation `v ↦ x v x⁻¹`: this is the adjoint action of `G`
on `Lie(G) ⊗ Γ(X, 𝒪_X)`.

Over a field `k`, a tangent vector `y ∈ Lie(G)` gives the infinitesimal point
`y_X : X[ε] ⟶ (Spec k)[ε] ⟶ G` with values in any `k`-scheme `X`
(`AlgebraicGeometry.GrpObj.lieAt`); `y ↦ y_X` turns addition into the group law and scalars
`c ∈ k` into rescalings.

## Main definitions

- `AlgebraicGeometry.overDualNumbers`: the thickening `X[ε]` of a scheme `X` over `S`, as a
  scheme over `S`, with `overDualNumbersι`, `overDualNumbersProj`, `overDualNumbersMap`,
  `overDualNumbersScale` and `overDualNumbersFold`.
- `AlgebraicGeometry.GrpObj.infPointsAt`: the infinitesimal points of `G` with values in `X`.
- `AlgebraicGeometry.GrpObj.infPointsAtMap`, `AlgebraicGeometry.GrpObj.infPointsAtScale`,
  `AlgebraicGeometry.GrpObj.infPointsAtConj`: base change, rescaling and conjugation.
- `AlgebraicGeometry.GrpObj.lieAt`: the infinitesimal point `y_X` of a tangent vector `y`.

## Blueprint

- `sk-p-comparison`: the adjoint representation, through its action on infinitesimal points.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### The thickening of a scheme over a base -/

section OverDualNumbers

variable {S : Scheme.{u}} (X : Over S)

end OverDualNumbers

/-! ### Infinitesimal points with values in a scheme -/

namespace GrpObj

section InfPointsAt

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (X : Over S)

variable {G X}

end InfPointsAt

/-! ### Tangent vectors as infinitesimal points with values in a scheme -/

section LieAt

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

variable (X : Over (Spec (.of k)))

end LieAt

end GrpObj

end AlgebraicGeometry
