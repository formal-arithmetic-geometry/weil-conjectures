/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Topological invariance of the small étale site

Let `f : X ⟶ Y` be a universal homeomorphism, i.e. integral, universally injective and
surjective. Then base change along `f` is an equivalence between the category of schemes
étale over `Y` and the category of schemes étale over `X`. This is [Stacks 04DZ].

The base change functor is `AlgebraicGeometry.Scheme.Hom.Etale`, so the statement is that
`f.Etale : Y.Etale ⥤ X.Etale` is an equivalence of categories; the bundled form is
`AlgebraicGeometry.Scheme.Hom.etaleEquivalence`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`: base change along a universal
  homeomorphism is an equivalence of small étale sites.
- `AlgebraicGeometry.Scheme.Hom.etaleEquivalence`: the same, as a bundled equivalence of
  categories `Y.Etale ≌ X.Etale`.

## Implementation notes

The mathematical content sits in the three instances `Hom.full_etale`,
`Hom.faithful_etale` and `Hom.essSurj_etale`, which are `sorry`ed here; the equivalence is
derived from them. The proof route intended for them, following [Stacks 04DZ], is:

- fullness and faithfulness: a universal homeomorphism stays a homeomorphism after any base
  change, so for étale `V, W` over `Y` the map `V ×_Y X ⟶ W ×_Y X` determines and is
  determined by `V ⟶ W`; concretely, morphisms of étale `Y`-schemes are determined by their
  graphs, which are open and closed in the relevant fibre products, and these open and
  closed sets correspond under the homeomorphisms induced by `f`;
- essential surjectivity: this is the substantial part. Stacks reduces to the case where `Y`
  is affine and, by writing the integral morphism `f` as a limit of finite ones, to the case
  of a nilpotent thickening; there it is the invariance of the étale site under nilpotent
  thickenings, i.e. the topological invariance of the étale site in the infinitesimal sense.

## References

* [Stacks 04DZ], Étale Cohomology, Theorem 59.45.2.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- Base change along a universal homeomorphism is full on small étale sites.
See https://stacks.math.columbia.edu/tag/04DZ. -/
@[stacks 04DZ]
instance Hom.full_etale : f.Etale.Full := sorry

/-- Base change along a universal homeomorphism is faithful on small étale sites.
See https://stacks.math.columbia.edu/tag/04DZ. -/
@[stacks 04DZ]
instance Hom.faithful_etale : f.Etale.Faithful := sorry

/-- Base change along a universal homeomorphism is essentially surjective on small étale
sites. See https://stacks.math.columbia.edu/tag/04DZ. -/
@[stacks 04DZ]
instance Hom.essSurj_etale : f.Etale.EssSurj := sorry

/-- **Topological invariance of the small étale site**: base change along a universal
homeomorphism `f : X ⟶ Y` is an equivalence between the category of schemes étale over `Y`
and the category of schemes étale over `X`.
See https://stacks.math.columbia.edu/tag/04DZ. -/
@[stacks 04DZ]
instance Hom.isEquivalence_etale : f.Etale.IsEquivalence where

/-- **Topological invariance of the small étale site**, [Stacks 04DZ]: for a universal
homeomorphism `f : X ⟶ Y`, the functor `V ↦ V ×_Y X` is an equivalence of categories
between schemes étale over `Y` and schemes étale over `X`. -/
@[stacks 04DZ]
noncomputable def Hom.etaleEquivalence : Y.Etale ≌ X.Etale :=
  f.Etale.asEquivalence

end AlgebraicGeometry.Scheme
