/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Morphisms with geometrically reduced fibres

Two facts about morphisms whose geometric fibres are reduced.

The first is that a smooth morphism has geometrically reduced fibres: its geometric fibres
are smooth varieties, hence regular, hence reduced. Together with the instances
`Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` of
`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, this is what makes a smooth morphism
satisfy the hypotheses of the statements below and of degree-zero flat base change.

The second is the étale-local slicing of such a morphism: a flat morphism, locally of
finite presentation, with geometrically reduced fibres admits an étale covering of its
source along which it factors through an étale morphism to the base, the remaining leg
being flat, locally of finite presentation, affine, with geometrically connected fibres
and admitting a section. The covering is recorded as an index type together with a jointly
surjective family of étale morphisms rather than as a bundled `Scheme.OpenCover`, since
the members of an étale cover are not open subschemes of the source.

## Main statements

- `AlgebraicGeometry.Smooth.geometricallyReduced`: a smooth morphism has geometrically
  reduced fibres.
- `AlgebraicGeometry.exists_etaleCover_factorization`: the étale-local slicing of a flat,
  locally finitely presented morphism with geometrically reduced fibres.

## References

- Stacks Project, More on Morphisms, Lemma 37.46.3,
  <https://stacks.math.columbia.edu/tag/0EY5>
- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism has geometrically reduced fibres: the geometric fibres of a smooth
morphism are smooth varieties over an algebraically closed field, hence regular, hence
reduced. -/
instance Smooth.geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f :=
  sorry

/-- Let `f : X ⟶ S` be flat, locally of finite presentation and with geometrically reduced
fibres. Then there is an étale covering `p i : U i ⟶ X` of `X`, that is, a family of étale
morphisms whose images cover `X`, such that each composite `p i ≫ f` factors as `q i ≫ r i`
with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` flat, locally of finite presentation and
affine, with geometrically connected fibres, and admitting a section:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```

A smooth morphism satisfies the hypotheses, by `AlgebraicGeometry.Smooth.geometricallyReduced`
and the instances `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation`; that special
case is Stacks `0EY4`, in which the first leg `q i` is moreover smooth. -/
@[stacks 0EY5]
theorem exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Flat (q i)) ∧ (∀ i, LocallyOfFinitePresentation (q i)) ∧
      (∀ i, IsAffineHom (q i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) :=
  sorry

end AlgebraicGeometry
