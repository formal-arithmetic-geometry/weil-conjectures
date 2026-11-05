/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.RelativePoints

/-!
# Infinitesimal points with values in a scheme form a free module

Let `G` be a group scheme locally of finite type over a field `k`, `X` a scheme over `k`, and
`(b_i)` a basis of `Lie(G)`. Every infinitesimal point `v : X[ε] ⟶ G` with values in `X` is
uniquely a product `∏ᵢ (b_i)_X(rᵢ ε)` of rescaled base changes of the `b_i`, with `rᵢ` global
functions on `X` (`AlgebraicGeometry.GrpObj.existsUnique_prod_eq`): the infinitesimal points with
values in `X` are `Lie(G) ⊗_k Γ(X, 𝒪_X)`.

The proof goes through an affine chart `j : Spec A ⟶ G` at the identity with a `k`-point `e` of
`A` over the identity. A point `v` has the same underlying map as the identity of `G(X)`, so it
factors through `j`; it is then given by a ring homomorphism `ψ_v : A → Γ(X, 𝒪_X)[ε]` of the form
`a ↦ e(a) + ε D_v(a)`, with `D_v` a derivation at `e`. The group law is the addition of the `D_v`
(the point `v_ε w_δ` over `X[ε][δ]` restricted along `δ = ε`), rescaling multiplies `D_v` by the
function, and a derivation at `e` is determined by its values on lifts `a_i ∈ ker e` of a basis
of `(ker e)/(ker e)²` dual to `(b_i)`, since `Lie(G)` is the dual of this cotangent space
(`AlgebraicGeometry.GrpObj.lieToDualCotangent`).

## Main statements

- `AlgebraicGeometry.GrpObj.isMulCommutative_infPointsAt`: the infinitesimal points with values in
  `X` commute.
- `AlgebraicGeometry.GrpObj.existsUnique_prod_eq`: they form a free `Γ(X, 𝒪_X)`-module with basis
  the base changes `(b_i)_X` of a basis of `Lie(G)`.

## Blueprint

- `sk-p-comparison`: `Lie(G) ⊗ A` as the infinitesimal points of `G` with values in `A`, on which
  `G(A)` acts by the adjoint action.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj IsMulCommutative

namespace AlgebraicGeometry

/-! ### Morphisms into an affine open subscheme -/

section LiftRingHom

variable {Y Y' Z : Scheme.{u}} {A : CommRingCat.{u}}

variable (j : Spec A ⟶ Z) [IsOpenImmersion j]

end LiftRingHom

/-! ### Global sections of the thickening maps -/

section AppTop

variable {X Y : Scheme.{u}}

end AppTop

namespace GrpObj

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

/-! ### Infinitesimal points in an affine chart -/

section Chart

variable {A : Type u} [CommRing A] [Algebra k A] {j : Spec (.of A) ⟶ G.left} [IsOpenImmersion j]

variable {e : A →ₐ[k] k}
  (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left)

variable (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  {x : Spec (.of A)} (hx : j x = onePoint G)

variable {I : Type u} [Fintype I] [DecidableEq I] (b : Module.Basis I k (Lie G))

end Chart

/-! ### The Lie algebra is finite-dimensional -/

/-! ### The infinitesimal points with values in a scheme form a free module -/

section Free

variable [LocallyOfFiniteType G.hom]

variable {I : Type u} [Fintype I] (b : Module.Basis I k (Lie G))

end Free

end GrpObj

end AlgebraicGeometry
