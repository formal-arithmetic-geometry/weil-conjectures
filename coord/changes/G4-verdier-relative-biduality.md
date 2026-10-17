# AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality

## Reason

Repair of returned delivery head `3806a6461`: restore the upstream interface verbatim.
The previous removal of the unrestricted theorem, the three absolute-exchange definitions,
and the public shriek-composition import was refused. All are restored. No existing type,
definition body, proof body or public import is changed from current main.

The unrestricted assertion is retained and marked `STATEMENT-DISPUTED`, with the singular-base
counterexample below. The return explicitly allows a needed variant in a `Sheaf` module.
`Sheaf.PoincareDuality.RelativeBiduality` now proves a separate conditional result for dualizable
objects when the relative dualizing complex is invertible, using the existing categorical
biduality theorem. This is not a proof of the original assertion and adds no hole.

Here is a counterexample satisfying every geometric hypothesis in the file.
Choose an algebraically closed field `k` of characteristic `p > 0`, and a
prime `ℓ ≠ p`. Put `S = Spec(k[x,y]/(xy))`, `X = Spec(k)`, and let
`a : X ⟶ S` be the origin. Both are separated and of finite type over `k`.
Write `Λ = ℚ̄_ℓ` and `A = Ra^! Λ_S`.

One can compute the costalk either by the punctured strict henselization,
or by normalization as follows. Let
`ν : A¹_k ⨿ A¹_k ⟶ S` be the normalization. There is a short exact sequence
`0 ⟶ Λ_S ⟶ ν_*Λ ⟶ a_*Λ ⟶ 0`: at the origin it is the diagonal inclusion
`Λ ⟶ Λ²` followed by the difference, and away from the origin the first
map is an isomorphism. A finite pushforward has no higher direct images.
Applying `Ra^!` and proper exchange with `ν` gives the triangle
`A ⟶ Λ(-1)²[-2] ⟶ Λ ⟶ A[1]`.
Here the two inverse images of the origin are regular closed points of
smooth affine lines, so the middle term is given by purity in codimension
one; also `Ra^!a_*Λ = Λ`. On the algebraically closed point the middle map
is zero, since it belongs to an `Ext²` group between finite-dimensional
vector spaces. Thus
`A ≅ Λ[-1] ⊕ Λ(-1)²[-2]`.

In particular `H¹(A) = Λ`, `H²(A) = Λ(-1)²`, and the other groups vanish.
For the bounded constructible object `K = Λ_X`, its first dual against
`A` is `A`, and its second dual is `RHom(A,A)`. The degree-zero cohomology
of the latter has dimension `1² + 2² = 5`. The degree-zero cohomology of
`K` has dimension one. Therefore the canonical biduality map is not an
isomorphism. This finite-dimensional calculation also holds for the
corresponding condensed coefficient objects and for their pro-étale
realizations.

The same costalk ranks follow directly from the localization triangle at
the node: the strict local scheme has constant cohomology `Λ` in degree
zero, and its punctured complement is the union of two punctured strict
local smooth curves, with cohomology `Λ²` in degree zero and `Λ(-1)²` in
degree one. The restriction in degree zero is the diagonal inclusion.
Strict local acyclicity is [Stacks, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO).
The finite-pushforward ingredient is
[Stacks, Section 59.55](https://stacks.math.columbia.edu/tag/03QN).
Purity here is just the usual closed-point purity for a smooth curve,
as in [Milne, Lectures on Etale Cohomology, Theorem 16.7](https://www.jmilne.org/math/CourseNotes/LEC.pdf),
applied first to the compatible finite coefficient systems and then to
their rational scalar extensions. No purity assertion about the singular
scheme `S` is used.

## Old

The current main declaration, retained verbatim:

```lean
theorem isIso_verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ a K) :=
  sorry
```

The returned sandbox had removed this declaration, `upperShriekDualizingComplexIso`,
`absoluteVerdierExchange`, `dualVerdierExchange`, and replaced the public `ShriekComposition`
import by `UpperShriek`.

## New

Every upstream declaration and import is restored verbatim. Only a dispute comment is added
immediately before the upstream theorem. Its original `sorry` remains.

The following separately named theorem is proved in the new module's unchanged geometric
context (the same `ℓ`, `k`, `X`, `S`, finite-type and separation assumptions):

```lean
theorem isIso_verdierBiduality_of_invertible_of_isDualizable
    (hω : IsInvertible (relativeDualizingComplex ℓ a))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hK : IsDualizable K) :
    IsIso (verdierBiduality ℓ a K) := by
  exact MonoidalClosed.isIso_toIhomIhom_of_isDualizable (Iso.refl _) hω hK
```

The existing categorical theorem applies directly because its double-dual map and
`Verdier.bidualityMap` are the same curry of braided evaluation.

## Users

No existing module changes its interface or needs adaptation. A whole-library text search
finds no consumer of the upstream unrestricted biduality theorem. The new theorem uses only
its map definition, never the disputed theorem. The existing source consumer and reexports
continue to see exactly their former declarations, instances, and imports.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Verdier | G4 | Restore all declarations and imports; add a dispute comment. |
| Sheaf.PoincareDuality.RelativeBiduality | G4, new module | Proves the conditional variant; no sorry. |
| WeilConjectures.PoincareDuality.Poincare | not adapted | Existing exchange theorem and public interface identical. |
| TargetsCheck | unclaimed | No target or dependency interface changes. |
| WeilConjectures | unclaimed | Reexported interface identical. |

No target needs statement review reopened: no existing statement or definition changes.
No unit route is pruned. The new conditional node cites the perfect-duality argument, but does
not import or apply a result about another coefficient category.

## Status

landed 20261017T021602-L-694355 2026-10-17 (merge of deliver/G4/WeilConjectures.PoincareDuality.Verdier)
