/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Topological invariance of the small étale site

Let `f : X ⟶ Y` be a universal homeomorphism, i.e. integral, universally injective and
surjective. Then base change along `f` is an equivalence between the category of schemes
étale over `Y` and the category of schemes étale over `X`, and it matches the small étale
topologies on the two sides. This is [Stacks 04DZ].

The base change functor is `AlgebraicGeometry.Scheme.Hom.Etale`; it sends an étale
`Y`-scheme `V` to the top-left corner of the cartesian square

```
   f.Etale.obj V = V ×_Y X ──→ V
            │                  │
            ↓                  ↓
            X ────────f───────→ Y
```

so the statement is that `f.Etale : Y.Etale ⥤ X.Etale` is an equivalence of categories,
with `AlgebraicGeometry.Scheme.Hom.etaleEquivalence` the bundled form.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.etaleEquivalence`: base change along a universal
  homeomorphism, as a bundled equivalence of categories `Y.Etale ≌ X.Etale`. This is the
  form in which the equivalence enters `CategoryTheory.Equivalence.sheafCongr`, hence the
  topos statements downstream.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff`
  (blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`): a sieve on an étale
  `Y`-scheme is a covering for the small étale topology of `Y` if and only if its base
  change along `f` is a covering for the small étale topology of `X`. Equivalently, a family
  of étale morphisms is jointly surjective if and only if its base change is.
- `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`
  (blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`): base change along a
  universal homeomorphism is an equivalence of the underlying categories of the small étale
  sites.
- `AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`: the two statements above combined,
  in the form `CategoryTheory.Functor.IsDenseSubsite` consumed by
  `CategoryTheory.Equivalence.sheafCongr`.

The two `#print axioms` guards at the end of the file pin this down: the comparison of the
topologies is `sorry`-free, and `Hom.isEquivalence_etale` is the single `sorry`.

## Implementation notes

The comparison of the topologies is proved here, following the last paragraph of the
blueprint proof of `lemma:weil-pbc-universal-homeomorphism-coverings` ("the omission in Tag
03SI"): a sieve is a covering for the small étale topology exactly when its arrows are
jointly surjective (`AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`), and for every
étale `V ⟶ Y` the projection `V ×_Y X ⟶ V` is a base change of `f`, hence a homeomorphism
on underlying spaces; so ranges of arrows correspond to ranges of their base changes under
these homeomorphisms. This uses nothing about `f.Etale` being an equivalence.

The equivalence itself, `Hom.isEquivalence_etale`, is the mathematical content of [Stacks
04DZ] and is `sorry`ed. The proof route of the blueprint is to construct a quasi-inverse by
descent: the diagonal `X ⟶ X ×_Y X` of a universal homeomorphism is a surjective closed
immersion, hence cut out by a nil ideal, and étale algebras are invariant under such a
quotient; this produces the canonical descent datum of
`lemma:weil-pbc-universal-homeomorphism-descent-datum`, and gluing the descended affine
pieces gives the quasi-inverse.

## References

* [Stacks 04DZ], Étale Cohomology, Theorem 59.45.2.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- The image of the base change of `g : V ⟶ U` along `f` is the preimage of the image of `g`
under the projection `U ×_Y X ⟶ U`, which is a base change of `f` and hence a homeomorphism
on underlying spaces. -/
lemma Hom.range_Etale_map_left {U V : Y.Etale} (g : V ⟶ U) :
    Set.range (f.Etale.map g).left = (pullback.fst U.hom f) ⁻¹' Set.range g.left :=
  range_eq_preimage_range_of_comm (f.Etale.map g).left (pullback.fst V.hom f)
    (pullback.fst U.hom f) g.left (pullback.fst U.hom f).injective
    (Hom.Etale_map_left_comp_fst f g)

/-- **Covering compatibility for universal homeomorphisms**: a sieve on an étale `Y`-scheme
`U` is a covering for the small étale topology of `Y` if and only if its base change along
the universal homeomorphism `f` is a covering for the small étale topology of `X`.

Equivalently, a family of étale morphisms to `U` is jointly surjective if and only if its
base change along `f` is: the projection `U ×_Y X ⟶ U` is a base change of `f`, hence a
homeomorphism, and it matches the images of the arrows of the sieve with the images of their
base changes.
(blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`) -/
@[stacks 04DZ]
lemma Hom.functorPushforward_mem_smallEtaleTopology_iff {U : Y.Etale} (S : Sieve U) :
    S.functorPushforward f.Etale ∈ X.smallEtaleTopology (f.Etale.obj U) ↔
      S ∈ Y.smallEtaleTopology U := by
  rw [mem_smallEtaleTopology_iff, mem_smallEtaleTopology_iff]
  constructor
  · intro h u
    obtain ⟨x, hx⟩ := (pullback.fst U.hom f).surjective u
    obtain ⟨W, k, ⟨V, g, l, hg, rfl⟩, hxk⟩ := h x
    refine ⟨V, g, hg, ?_⟩
    have hsub : Set.range (l ≫ f.Etale.map g).left ⊆ Set.range (f.Etale.map g).left :=
      range_comp_subset_range l.left (f.Etale.map g).left
    rw [← hx]
    exact (Hom.range_Etale_map_left f g).le (hsub hxk)
  · intro h x
    obtain ⟨V, g, hg, hx⟩ := h ((pullback.fst U.hom f) x)
    exact ⟨f.Etale.obj V, f.Etale.map g, Presieve.image_mem_functorPushforward _ _ hg,
      (Hom.range_Etale_map_left f g).ge hx⟩

-- TODO: prove; see [Stacks 04DZ] and the proof route in the implementation notes above.
/-- **Topological invariance of the small étale site**: base change along a universal
homeomorphism `f : X ⟶ Y` is an equivalence between the category of schemes étale over `Y`
and the category of schemes étale over `X`.

This is not an instance while it is `sorry`ed, so that no downstream result depends on the
`sorry` invisibly.
(blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`) -/
@[stacks 04DZ]
theorem Hom.isEquivalence_etale : f.Etale.IsEquivalence := sorry

attribute [local instance] Hom.isEquivalence_etale

/-- **Topological invariance of the small étale site**, [Stacks 04DZ]: for a universal
homeomorphism `f : X ⟶ Y`, the functor `V ↦ V ×_Y X` is an equivalence of categories
between schemes étale over `Y` and schemes étale over `X`.

This bundled form is what `CategoryTheory.Equivalence.sheafCongr` consumes, see
`AlgebraicGeometry.Etale.sheafEquivalence`.
(blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`) -/
@[stacks 04DZ]
noncomputable def Hom.etaleEquivalence : Y.Etale ≌ X.Etale :=
  f.Etale.asEquivalence

/-- Base change along a universal homeomorphism exhibits the small étale site of `Y` as a
dense subsite of the small étale site of `X`: it is an equivalence of the underlying
categories by `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`, and it reflects coverings
by `AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff`. -/
theorem Hom.isDenseSubsite_etale :
    f.Etale.IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology where
  functorPushforward_mem_iff := Hom.functorPushforward_mem_smallEtaleTopology_iff f _

end AlgebraicGeometry.Scheme

/-- info: 'AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff

/-- info: 'AlgebraicGeometry.Scheme.Hom.isEquivalence_etale' depends on axioms: [propext, sorryAx,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isEquivalence_etale
