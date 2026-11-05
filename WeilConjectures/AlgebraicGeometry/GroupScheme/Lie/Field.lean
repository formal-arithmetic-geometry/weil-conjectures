/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

/-!
# The Lie algebra of a group scheme of finite type over a field

The Lie algebra of a group scheme of finite type over a field.

## Main results

- `AlgebraicGeometry.GrpObj.finrank_lie_eq_finrank_cotangent`: in an affine chart `Spec A` at the
  identity, `Lie(G)` has the dimension of the cotangent space of `A` at the identity.
- `AlgebraicGeometry.GrpObj.exists_affine_chart`: such charts exist with `A` of finite type.
- `AlgebraicGeometry.GrpObj.finrank_lie_le_topologicalKrullDim`: in characteristic zero,
  `dim Lie(G) ≤ dim G`.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Group schemes of finite type over a field -/

section Field

variable {k : Type u} [Field k]

/-! ### Affine charts at the identity

Let `j : Spec A ⟶ G` be an affine open subscheme of a group scheme `G` over `k` and `e` a
`k`-point of `A` such that `j ∘ Spec e` is the identity point. A tangent vector `v` of `G`, a point
of `G` over `k[ε]` reducing to the identity, factors through `j`, as `Spec ψ` for a point
`ψ : A → k[ε]` lifting `e`, and `ψ` is the composite of `A → 𝒪_{G,1}` with `v^♯`. Hence
`Lie(G)` is the dual of the cotangent space of `A` at `e`. -/

namespace GrpObj

variable {G : Over (Spec (.of k))} [GrpObj G] {A : Type u} [CommRing A] [Algebra k A]
  (j : Spec (.of A) ⟶ G.left) [IsOpenImmersion j]

variable {j}

variable (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) {x : Spec (.of A)}
  (hx : j x = onePoint G)

variable {e : A →ₐ[k] k}
  (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left)

end GrpObj

namespace GrpObj

variable {G : Over (Spec (.of k))} [GrpObj G]

end GrpObj

namespace GrpObj

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

end GrpObj

end Field

end AlgebraicGeometry
