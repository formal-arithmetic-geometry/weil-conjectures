/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.AffineFinitePresentation
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.BaseChange
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.ClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.DescendsToStage
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Gluing
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Iso
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Separated
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.FinitePresentationApproximation
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.FinitePresentationModel
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.MinimalCounterexample
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Separated
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.SeparatingPair
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Basic
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Existence
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Basic
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Charts
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Cofiltered
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Cone
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Diagram
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.ExistsStage
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Limit

/-!
# Cofiltered limits of schemes with affine transition morphisms

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.NoetherianApproximation` and
`WeilConjectures.AlgebraicGeometry.AffineTransitionLimit`; it was split to keep the compilation
of each part cheap.

## Noetherian approximation of quasi-compact quasi-separated schemes

A *Noetherian approximation* of a scheme `S` is a cofiltered system of schemes of finite type
over `ℤ` with affine transition morphisms, together with a limit cone over the system with
point `S` (`AlgebraicGeometry.Scheme.NoetherianApproximation`). The stages of such a system
are Noetherian schemes (`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`).

Absolute Noetherian approximation (Stacks Project Tag 01ZA), proved in
`WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Existence` as
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, asserts that every quasi-compact
quasi-separated scheme admits a Noetherian approximation. It is proved by induction over a
finite affine cover, starting from the affine case: for an affine scheme `S`, the spectra of the
finitely generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a Noetherian approximation
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The key algebraic input
is that `Γ(S, ⊤)` is the filtered colimit of its finitely generated `ℤ`-subalgebras
(`CommRingCat.isColimitFgSubalgebraCocone`), and the geometric translation is that `Spec`,
being a right adjoint, preserves limits.

Throughout, "of finite type over `ℤ`" is spelled out as `LocallyOfFiniteType` of the
structure morphism `specULiftZIsTerminal.from X : X ⟶ Spec ℤ` together with
`CompactSpace X`.

(Blueprint: `def:nagata-noetherian-inverse-system`, `prop:nagata-noetherian-inverse-system`.)

## Checking the limit property locally on a stage

Mathlib's `AlgebraicGeometry.isLimitOpensCone` says that a limit cone over a cofiltered diagram
`{Dᵢ}` of schemes restricts, over any open `V ⊆ Dᵢ`, to a limit cone over the diagram of the
preimages of `V`. Here we prove the converse: a cone `c` over `{Dᵢ}` is a limit cone as soon as
its restrictions to the members of an open cover of one stage, and to their pairwise
intersections, are limit cones (`AlgebraicGeometry.isLimitOfIsLimitOpensCone`). No assumption on
the transition morphisms is needed. This is how the limit property of the system constructed for
Tag 01ZA is verified, chart by chart.

## The stages of the induction step of absolute Noetherian approximation

The general case of Tag 01ZA is proved by induction over a finite affine cover, extending an
approximation of a quasi-compact open `U` of `X` across one more affine open `V`
(Stacks Project Tag 07RN). The data of one induction step is bundled into
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData`, and the index category of
the extended system is the category
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.Stage` of *stages*: a stage
consists of an index `j` of the approximation of `U`, lifts to the stage `j` of finitely many
sections of `V` whose basic opens cover `W = U ⊓ V`, and a finitely generated `ℤ`-subalgebra
`A` of the fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)` big enough that `Wⱼ` becomes a
quasi-affine open of `Spec A` (`Stage.isOpenImmersion_toSpec`, Tags 01Z7 and 01Z9).

The two structural facts that drive the induction are that the stages form a cofiltered
category, and that the functor `ExtensionData.stageIndex` remembering the underlying index is
initial; so limits over the system of the `Wⱼ` may be computed over the category of stages.

## Descending schemes of finite presentation along an inverse limit of affine schemes

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps. If `X`
is an affine scheme that is locally of finite presentation over `lim Dᵢ`, then `X` is the base
change of an affine scheme that is locally of finite presentation over one of the `Dᵢ`
(`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`).

The same holds for an arbitrary scheme `X` of finite presentation over `lim Dᵢ`, and more
generally over a limit of quasi-compact quasi-separated schemes
(`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, Stacks Project Tag 01ZM):
one covers `X` by finitely many affine opens, each lying over an affine open of a fixed stage,
and glues the finite-stage models of the charts over a common stage. The two auxiliary steps
are that a quasi-compact open of `X` descends to a stage
(`AlgebraicGeometry.exists_descendsAtWithOpen`) and that two finite-stage models of the
same scheme become isomorphic at a later stage
(`AlgebraicGeometry.exists_iso_of_isPullback`).

## Separatedness descends to a finite stage

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps. If the limit `lim Dᵢ` is a separated scheme, then `Dᵢ` is separated for every
`i` past some stage (`AlgebraicGeometry.Scheme.exists_isSeparated_of_isLimit`, Stacks Project
Tag 086Q); and if all the `Dᵢ` lie over a fixed base `S` and `lim Dᵢ ⟶ S` is separated, then
`Dᵢ ⟶ S` is separated for every `i` past some stage
(`AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit`, Stacks Project Tag 01ZH).

Both are proved through the affine criterion `AlgebraicGeometry.IsSeparatingPair`: a scheme is
separated as soon as the affine opens of a finite affine cover pairwise have affine intersections
and the sections over such an intersection are generated by the sections of the two members. The
affineness of the intersections descends to a stage by Mathlib's
`AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` (Stacks Project Tag 01Z6). The generation
statement descends because, on one hand, the sections over the intersection at a stage are
finitely generated over the sections of one of the two members, and on the other hand the
elements of the limit which do come from a stage inside the subring generated by the two members
form a subring, which by hypothesis is everything
(`AlgebraicGeometry.exists_isSeparatingPair_of_isLimit`).

## The finite presentation model system of a morphism of finite type

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ S` be a morphism locally of
finite type with `X` quasi-compact and quasi-separated. Then `X` is a cofiltered limit of
schemes of finite presentation over `S` whose transition morphisms and whose morphisms from `X`
are closed immersions. Such a system is bundled into
`AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation`, and its existence is
`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation` (Stacks Project
Tag 09ZQ).

It is obtained by shrinking the immersion of Tag 01ZE to a closed immersion `X ⟶ Y` into a
quasi-compact open of the model
(`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation`) and then
writing `X` as the limit of the closed subschemes of `Y` cut out by the subideal sheaves of
finite type of the kernel of `X ⟶ Y` (Tag 09ZP).

## Minimal counterexamples over a quasi-compact quasi-separated base

A property `P` of quasi-compact quasi-separated schemes over a fixed quasi-compact
quasi-separated base `T` — a predicate on morphisms `T' ⟶ T` — is *qcqs-local*
(`AlgebraicGeometry.Scheme.IsQcqsLocalProperty`) if it is invariant under thickenings,
compatible with cofiltered limits along affine transition morphisms, propagates from a
scheme to a quasi-compact open subscheme or to its closed complement, and fails for the empty
scheme. Such a property holds
for the spectrum of a field over `T` as soon as it holds for `T` itself
(`AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`). Applied to the failure locus
of a base-change map, this says that a minimal counterexample can be found over a point.

Since Mathlib has no notion of a thickening of schemes, a thickening is spelled out as a
closed immersion which is surjective on points.

## References

- [Stacks: Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
- [Stacks: Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
- [Stacks: Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
- [Stacks: Tag 01ZH](https://stacks.math.columbia.edu/tag/01ZH)
- [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
- [Stacks: Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
- [Stacks: Tag 086Q](https://stacks.math.columbia.edu/tag/086Q)
- [Stacks: Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
- [Stacks: Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
-/
