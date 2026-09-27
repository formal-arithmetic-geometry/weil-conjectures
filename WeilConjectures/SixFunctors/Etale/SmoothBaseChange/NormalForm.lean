/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!
# Étale-local normal form and slicing

A smooth morphism is étale-locally on the source a composite of an étale morphism with a
projection from an affine space. This file states two forms of that fact.

The first, `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`, is the pointwise normal
form: if `g : X ⟶ Y` is smooth of relative dimension `d` and `x : X`, then there are affine
open neighbourhoods `V` of `x` and `U` of `g.base x` with `V ≤ g ⁻¹ᵁ U` such that the
restricted morphism `g.resLE U V` factors as an étale morphism `V ⟶ 𝔸(d; U)` followed by the
structure morphism `𝔸(d; U) ↘ U`. (The index type of the affine space is `ULift.{u} (Fin d)`,
since `AlgebraicGeometry.AffineSpace` takes an index type in the same universe as the scheme.)

The second, `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`, is the slicing
statement: a smooth `f : X ⟶ S` admits an étale covering `p i : U i ⟶ X` such that each
composite `U i ⟶ X ⟶ S` factors through a morphism `V i ⟶ S` which is étale, the first leg
`U i ⟶ V i` being smooth, affine, with geometrically connected fibres, and admitting a
section. The covering is recorded as an index type together with a jointly surjective family
of étale morphisms rather than as a bundled `Scheme.OpenCover`, since the members of an étale
cover are not open subschemes of `X`.

Both statements are the content of the blueprint subsection `sk-prop-normal-form`; the proofs
are not given here.

## Main statements

- `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`: the étale-local normal form of a
  smooth morphism of relative dimension `d`.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the slicing of a smooth
  morphism through étale morphisms with geometrically connected smooth affine fibres.

## References

- Stacks Project, Tag `054L`, <https://stacks.math.columbia.edu/tag/054L>
- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-prop-normal-form`: Étale-local normal form and slicing

Let `g : X ⟶ Y` be smooth of relative dimension `d` and let `x : X`. After replacing `X` and
`Y` by affine open neighbourhoods `V ∋ x` and `U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U`, the morphism
`g` factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection
`𝔸(d; U) ↘ U`. -/
@[stacks 054L]
theorem Smooth.exists_etale_to_affineSpace {X Y : Scheme.{u}} (g : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d g] (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU :=
  sorry

/-- Blueprint `sk-prop-normal-form`: Étale-local normal form and slicing

Let `f : X ⟶ S` be smooth. Then there is an étale covering `p i : U i ⟶ X` of `X`, that is, a
family of étale morphisms whose images cover `X`, such that each composite `p i ≫ f` factors
as `q i ≫ r i` with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` smooth and affine, with
geometrically connected fibres, and admitting a section. -/
@[stacks 0EY4]
theorem Smooth.exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Smooth (q i)) ∧ (∀ i, IsAffineHom (q i)) ∧
      (∀ i, GeometricallyConnected (q i)) ∧ (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧
      (∀ i, q i ≫ r i = p i ≫ f) :=
  sorry

end AlgebraicGeometry
