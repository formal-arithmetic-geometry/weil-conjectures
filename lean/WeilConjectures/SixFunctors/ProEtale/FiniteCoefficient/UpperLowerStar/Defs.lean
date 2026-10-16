/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!

# The pushforward `g_*` and the pullback `g^*` on small pro-étale sites

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, for mathlib's pro-étale site
`AlgebraicGeometry.Scheme.ProEt.topology`: the topology on the category `X.ProEt` of
weakly étale schemes over `X` whose covers are the pro-étale covers of
[Bhatt–Scholze, Definition 4.1.1], that is, the fpqc covers by weakly étale morphisms.

For an *arbitrary* morphism of schemes `g : Z ⟶ Y`, base change induces the functor
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ g : Y.ProEt ⥤ Z.ProEt` between the small
pro-étale sites, and composition with it defines the pushforward `g_*` on `A`-valued
pro-étale sheaves. Its left adjoint `g^*` is the left Kan extension on presheaves followed
by sheafification.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStar`: the pushforward `g_*`, given by composition with
  the base change functor, with scoped notation `(g)_*[A]`.
- `AlgebraicGeometry.ProEtale.upperStar`: the pullback `g^*`, given by left Kan extension
  on presheaves followed by sheafification, with scoped notation `(g)^*[A]`.
- `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.lowerStarId` and `AlgebraicGeometry.ProEtale.upperStarId`: the
  identity isomorphisms `(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`, the latter obtained from the former
  by uniqueness of left adjoints.
- `AlgebraicGeometry.ProEtale.lowerStarComp` and
  `AlgebraicGeometry.ProEtale.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`: base change along an
  arbitrary morphism is continuous for the pro-étale topologies. It preserves covers since
  pro-étale covers are stable under base change, and it preserves compatible families since
  it is representably flat, being a finite-limit-preserving functor on the finitely
  complete pro-étale slice. It is proved in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`, and it is what makes
  `ProEtale.lowerStar` carry no hypotheses at all.
- `AlgebraicGeometry.ProEtale.isLeftAdjoint_op_overPullback` and
  `AlgebraicGeometry.ProEtale.hasPointwiseLeftKanExtension_op_overPullback`: for `g` weakly
  étale, the opposite of base change is a left adjoint — base change is right adjoint to
  the localization functor `MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›` — and all pointwise
  left Kan extensions along it exist. For a general `g` the pointwise left Kan extensions
  instead exist by essential `u + 1`-smallness of the indexing comma categories,
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, with no smallness of
  the small pro-étale site itself.
- `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_lowerStar` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerStar`: the pushforward `g_*`
  preserves every limit that exists in the coefficient category. This needs no hypothesis
  beyond the continuity of the base change functor, in particular it does not use the
  adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`: the pullback `g^*` is left
  exact, hence exact, being also a left adjoint. In contrast to `g_*` this is not
  automatic: it needs sheafification to be left exact and the left Kan extension along the
  opposite of base change to be so as well. For a weakly étale `g` the latter is proved
  here, the Kan extension being precomposition with a right adjoint; for a general `g` it is
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u + 1`, one above the universe `u` of the base schemes, following the
  convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, which
  requires `WeaklyEtale g`. This is essential for compactifications, whose structure morphism is
  proper and in general is not weakly étale.
- Sheafification on the small pro-étale sites and the left Kan extensions along the
  opposite of base change both hold for every Grothendieck abelian `A`, so
  `ProEtale.upperStar` and the adjunction `g^* ⊣ g_*` carry no hypotheses either.
  Sheafification is
  `CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, still sorried through
  `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` there, and it does
  use essential smallness of the site. The Kan extensions are proved and use no smallness
  of the site at all, only of the indexing comma categories, see
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

-/

-- Compatibility re-export: all shared declarations belong to the ordinary module.
