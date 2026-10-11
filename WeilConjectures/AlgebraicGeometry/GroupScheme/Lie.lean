/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.PointOfDerivation
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The Lie algebra of a group scheme

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`; it was split to keep the compilation of each
part cheap.

Let `G` be a group scheme over a scheme `S`, with structure morphism `f : G ⟶ S`, identity
section `e : S ⟶ G` and multiplication `m : G ×_S G ⟶ G`. Set `ω_{G/S} = e^*Ω¹_{G/S}`. The *Lie
algebra sheaf* of `G/S` is the `𝒪_S`-module

$$
\operatorname{Lie}(G/S) = \mathcal{H}om_{\mathcal O_S}(\omega_{G/S}, \mathcal O_S),
$$

the sheaf of relative tangent vectors along the identity section, and the *Lie algebra*
`Lie(G) = Hom_{𝒪_S}(ω_{G/S}, 𝒪_S)` is its module of global sections. When `G ⟶ S` is smooth,
`ω_{G/S}` is locally free and `Lie(G/S) ≅ e^*T_{G/S}` is the pullback of the tangent sheaf; for an
arbitrary group scheme the dual-of-cotangent definition is the right one.

## Infinitesimal points

The dual-number thickening `S[ε]` of the base (`AlgebraicGeometry.Scheme.dualNumbers`) is a scheme
over `S` through the projection `p : S[ε] ⟶ S`, and the closed immersion `i : S ⟶ S[ε]`, `ε ↦ 0`,
is a section of `p`. The *infinitesimal points* of `G` are the points `v : S[ε] ⟶ G` over `S` with
`i ≫ v = e`; they form a normal subgroup `infPoints G` of the group `G(S[ε])`, whose group law is
the addition of tangent vectors. A point `v` has the same underlying map as `e`, and on functions
`v^♯(a) = e^♯(a) + ε d_v(a)`; the `ε`-coefficient `d_v` is a derivation `𝒪_G → e_*𝒪_S` over
`f⁻¹𝒪_S`, that is a morphism `Ω¹_{G/S} ⟶ e_*𝒪_S`, that is an element of
`Lie(G) = Hom(e^*Ω¹_{G/S}, 𝒪_S)`. This is the bridge `GrpObj.toLie : infPoints G → Lie G`, a
bijection (`GrpObj.lieEquiv`).

## The bracket

Over the two-parameter thickening `S[ε][δ]`, a point `v : S[ε] ⟶ G` gives `v_ε` and `v_δ` by the
two projections. The commutator `c(v, w) = v_ε w_δ v_ε⁻¹ w_δ⁻¹` reduces to the identity both for
`ε = 0` and for `δ = 0`, and the points of `G` over `S[ε][δ]` with this property are in bijection
with `infPoints G` through `η ↦ εδ` (`GrpObj.mixedEquiv`). The Lie bracket is the mixed term of the
commutator,

$$
[v, w] = \mu^{-1}(v_ε w_δ v_ε^{-1} w_δ^{-1}),
$$

transported to `Lie(G)` along the bridge. This is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields `ṽ(g, d) = g v(d)` extending `v` and `w`: the
pullback of right multiplication by `v_ε` on the functions of `G[ε]` is `1 + ε D_v`, so that of
`c(v, w)` is `1 + εδ (D_v D_w - D_w D_v)`. For an affine `G = Spec A` it is the convolution
commutator `(v ⊗ w - w ⊗ v) ∘ Δ` of point derivations at the counit. For `G = GL_n`, where the
infinitesimal points are the matrices `1 + εX`, it is the matrix commutator, and
`Lie(GL_n) = gl_n`; see `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`, and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie` for the Lie
algebras of the closed subgroup schemes of `GL_n`.

## Main definitions

- `AlgebraicGeometry.GrpObj.unitSection`, `AlgebraicGeometry.GrpObj.omega`,
  `AlgebraicGeometry.GrpObj.lieAlgebraSheaf`: the identity section, `ω_{G/S}` and `Lie(G/S)`.
- `AlgebraicGeometry.GrpObj.Lie`: the Lie algebra `Lie(G) = Hom(ω_{G/S}, 𝒪_S)`, a module over
  `Γ(S, 𝒪_S)`, and over `R` when `S = Spec R`, with its `LieRing` and `LieAlgebra` structures.
- `AlgebraicGeometry.GrpObj.infPoints`: the infinitesimal points `ker(G(S[ε]) → G(S))`, and the
  bridge `AlgebraicGeometry.GrpObj.lieEquiv : infPoints G ≃ Lie G`.
- `AlgebraicGeometry.GrpObj.differential`: the differential `Lie(G) →ₗ⁅R⁆ Lie(H)` of a
  homomorphism of group schemes over `R`.
- `AlgebraicGeometry.tangentGroup`, `AlgebraicGeometry.GrpObj.infPointsEquivTangentGroup`: for `G`
  over `Spec R`, the infinitesimal points are the points with values in the ring of dual numbers
  `R[ε]` reducing to the identity.
- `AlgebraicGeometry.GrpObj.lieEquivIdentityComponent`: `Lie(G°) = Lie(G)` for a group scheme of
  finite type over a field.

## Main results

- `AlgebraicGeometry.GrpObj.lieAlgebraSheaf_iso_pullback_tangentSheaf`: for smooth `G ⟶ S`,
  `Lie(G/S) ≅ e^*T_{G/S}`.
- `AlgebraicGeometry.GrpObj.differential_injective`: a monomorphism of group schemes has an
  injective differential; `AlgebraicGeometry.GrpObj.differential_bijective_of_isOpenImmersion`: an
  open immersion of group schemes has a bijective differential.
- `AlgebraicGeometry.GrpObj.lie_mem_range_differential_of_commutator_mem`: if the commutators of
  `H` factor through a subgroup scheme `G ⟶ H`, then the brackets of tangent vectors of `H` are
  tangent to `G`.
- `AlgebraicGeometry.GrpObj.range_differential_le_center`: the tangent vectors of a central
  subgroup scheme are central in the Lie algebra.
- `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim`: in characteristic zero the Lie
  algebra has the dimension of the group (Cartier's theorem).

## Implementation notes

All constructions are genuine definitions. The bridge `toLie` is a bijection: its inverse sends a
derivation `d : 𝒪_G → e_*𝒪_S` to the point `GrpObj.pointOfDerivation`, `a ↦ e^♯(a) + ε d(a)`.
The proofs that are still missing (the sheaf and local conditions of the thickening, the
bijectivity of the mixed-term map, the Lie algebra axioms, and the functoriality of the bracket)
are recorded as `sorry`. The base ring of a
group scheme over an affine base is written `R`; `k` is reserved for a field.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: the Lie algebra of a central subgroup scheme.
-/
