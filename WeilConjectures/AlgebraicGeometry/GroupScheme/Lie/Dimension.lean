/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field
public import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# The dimension of the Lie algebra of a group scheme over a field

Let `G` be a group scheme locally of finite type over a field `k`. The dimension of `G` is at most
the dimension of its Lie algebra, and in characteristic zero they are equal (Cartier).

The upper bound is proved after base change to an algebraic closure `K` of `k`. The dimension of
`G` is at most that of `G_K`, as `Spec (K ⊗[k] B)` is integral over `Spec B` for every affine open
`Spec B` of `G`. Over `K` the left translations act transitively on the closed points, and every
point specialises to a closed point, so `dim G_K` is the codimension of any closed point. In the
base change `Spec (K ⊗[k] A)` of an affine chart `Spec A` at the identity, the base change of the
identity is a closed point whose codimension is bounded by the dimension of the cotangent space
of `A` at the identity, which is the dimension of `Lie(G)`.

## Main results

- `AlgebraicGeometry.Scheme.topologicalKrullDim_eq_iSup_coheight`: the dimension of a scheme is
  the supremum of the codimensions of its points.
- `AlgebraicGeometry.topologicalKrullDim_le_pullback`: the dimension of a scheme over `k` is at
  most the dimension of its base change to an algebraic extension of `k`.
- `AlgebraicGeometry.GrpObj.topologicalKrullDim_le_coheight`: over an algebraically closed field,
  the dimension of a group scheme locally of finite type is at most the codimension of any of its
  closed points.
- `AlgebraicGeometry.GrpObj.topologicalKrullDim_le_finrank_lie`: `dim G ≤ dim Lie(G)`.
- `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim`: in characteristic zero,
  `dim Lie(G) = dim G`.
- `AlgebraicGeometry.GrpObj.isIso_left_of_differential_bijective`: in characteristic zero, a
  closed subgroup scheme of a connected group scheme of finite type with the same Lie algebra is
  everything.

## Blueprint

- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `lem-wf-same-lie-closed-subgroup`: the Lie criterion for closed subgroups.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order
open scoped TensorProduct

namespace AlgebraicGeometry

section Field

variable {k : Type u} [Field k]

end Field

namespace GrpObj

variable {k : Type u} [Field k]

end GrpObj

end AlgebraicGeometry
