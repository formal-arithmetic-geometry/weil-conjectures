/-
Copyright (c) 2026 Weil Conjectures Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures Contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Sheafification with Grothendieck abelian coefficients, reduced to genuinely small sites

`WeilConjectures/CategoryTheory/GrothendieckAbelian/HasSheafify.lean` asserts, with a `sorry`,
that `A`-valued presheaves on the small `Q`-site of `P`-schemes can be sheafified when `A` is
Grothendieck abelian. Its docstring says the proof is "the sites are essentially small and `A`
is complete and cocomplete with exact filtered colimits, so the plus-construction applies".

That route does not close in Mathlib as it stands, and this file records exactly where it stops.
**Mathlib has no `HasSheafify J A` — indeed no `HasWeakSheafify J A` — for `J` a Grothendieck
topology on a genuinely small category and `A` merely Grothendieck abelian.** The only
construction of sheafification for a general topology is the plus-plus construction of
`Mathlib/CategoryTheory/Sites/LeftExact.lean`, which needs `A` *concrete*:
`ConcreteCategory A`, `PreservesLimits (forget A)`, `HasFiniteLimits A` and
`∀ X, Small (J.Cover X)`.

Everything *downstream* of that base case is already coefficient-agnostic, and this file proves
it. The three results below take, as an explicit hypothesis, sheafification on every genuinely
small site, and derive sheafification on an essentially small site, on a site with an essentially
small dense subsite, and finally on the small étale site of a scheme. All three are `sorry`-free.

## Main results

* `CategoryTheory.HasSheafifySmallSites`: the remaining obligation, named — `A` admits
  sheafification of presheaves on every Grothendieck topology on every genuinely small category.
* `CategoryTheory.hasSheafifySmallSites_addCommGrpCat`: it holds for a concrete coefficient
  category, so the obligation is not vacuous.
* `CategoryTheory.hasSheafify_of_essentiallySmall`: it transports to essentially small sites.
* `CategoryTheory.hasSheafify_of_isDenseSubsite`: it transports along an essentially small dense
  subsite whose sheaf-pushforward is an equivalence, with **no** concreteness on `A`.
* `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology_of_hasSheafifySmallSites`: hence it
  gives sheafification on the small étale site, via Mathlib's affine dense subsite.

## Why the small étale site needs the dense-subsite step

`hasSheafify_of_essentiallySmall` cannot be applied to `X.smallEtaleTopology` directly: the
small étale site of a scheme is *provably not* essentially small, since `∐ (i : I), X` is étale
over `X` and these objects are pairwise non-isomorphic for non-equinumerous `I`. Mathlib's
`AlgebraicGeometry.Scheme.AffineEtale` is the essentially small dense subsite that repairs this,
and `Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` — which asks only for
`HasFiniteLimits A` — is what transports across it.

## Scope

Nothing here proves the sorried instance; a `sorry`-free proof of `HasSheafifySmallSites A` for
Grothendieck abelian `A` is still needed, and is the whole remaining content. What is
established is that such a proof is *sufficient* for the étale case, so no further site-theoretic
work is required once it exists. See the module docstring of
`WeilConjectures/CategoryTheory/GrothendieckAbelian/HasSheafify.lean`.
-/

@[expose] public section

universe u' u u₂ u₃

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- `A` admits sheafification of `A`-valued presheaves on *every* Grothendieck topology on
*every* genuinely small category with `Hom`-types in `u`.

For a concrete `A` this is Mathlib's plus-plus construction (the anonymous `HasSheafify`
instance near the end of `Mathlib/CategoryTheory/Sites/LeftExact.lean`). For a merely
Grothendieck abelian `A` it is unproved — that is the single remaining obligation behind
`CategoryTheory.GrothendieckTopology.hasSheafify_smallGrothendieckTopology`, and this file
exists to show it is the *only* one. -/
def HasSheafifySmallSites (A : Type u') [Category.{u} A] : Prop :=
  ∀ (C : Type u) [SmallCategory C] (J : GrothendieckTopology C), HasSheafify J A

/-- The obligation is not vacuous: for a *concrete* coefficient category Mathlib's plus-plus
construction supplies it, and `AddCommGrpCat` is a witness.

This is the exact sense in which `HasSheafifySmallSites` is the coefficient-category axis of the
problem rather than a site-theoretic one: the statement below is `sorry`-free, and everything
that fails for a general Grothendieck abelian `A` fails here and only here. -/
theorem hasSheafifySmallSites_addCommGrpCat :
    HasSheafifySmallSites.{u + 1, u} AddCommGrpCat.{u} :=
  fun _ _ _ ↦ inferInstance

/-- Sheafification on genuinely small sites transports to essentially small sites. -/
theorem hasSheafify_of_essentiallySmall {C : Type u₂} [Category.{u} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{u} A]
    (h : HasSheafifySmallSites.{u'} A) :
    HasSheafify J A :=
  haveI := h (SmallModel C) ((equivSmallModel C).inverse.inducedTopology J)
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Sheafification on genuinely small sites transports along an essentially small dense subsite
whose sheaf-pushforward functor is an equivalence.

The only hypothesis on the coefficient category beyond `Category.{u} A` is `HasFiniteLimits A`,
which an abelian category supplies; in particular there is no concreteness here. -/
theorem hasSheafify_of_isDenseSubsite {C : Type u₂} [Category.{u} C] {D : Type u₃} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [EssentiallySmall.{u} C] [G.IsDenseSubsite J K]
    (A : Type u') [Category.{u} A] [HasFiniteLimits A]
    [(G.sheafPushforwardContinuous A J K).IsEquivalence]
    (h : HasSheafifySmallSites.{u'} A) :
    HasSheafify K A :=
  haveI := hasSheafify_of_essentiallySmall J A h
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K G

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Sheafification on genuinely small sites gives sheafification on the small **affine** étale
site of a scheme, which is essentially small (the anonymous `EssentiallySmall` instance in
`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`). -/
theorem hasSheafify_affineEtaleTopology_of_hasSheafifySmallSites (S : Scheme.{u}) (A : Type u')
    [Category.{u} A] (h : HasSheafifySmallSites.{u'} A) :
    HasSheafify (AffineEtale.topology S) A :=
  hasSheafify_of_essentiallySmall _ A h

/-- Sheafification on genuinely small sites gives sheafification on the small étale site of a
scheme, for any Grothendieck abelian coefficient category.

This is the étale instantiation of
`CategoryTheory.GrothendieckTopology.hasSheafify_smallGrothendieckTopology`, conditional on the
one obligation Mathlib does not supply. The small étale site is not itself essentially small, so
the proof goes through the affine dense subsite. -/
theorem hasSheafify_smallEtaleTopology_of_hasSheafifySmallSites (S : Scheme.{u}) (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (h : HasSheafifySmallSites.{u'} A) :
    HasSheafify S.smallEtaleTopology A :=
  haveI := hasSheafify_affineEtaleTopology_of_hasSheafifySmallSites S A h
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

end AlgebraicGeometry.Scheme
