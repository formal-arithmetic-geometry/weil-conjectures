/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Curve families are schemes étale locally on the base

Source: Stacks Project, moduli-curves.tex, Tag 0E6F, first assertion, and
section-stack-curves (blueprint: lem-sfb-curve-etale-scheme-cover).

The existing curve-family predicate retains algebraic-space sources and allows empty
and zero-dimensional geometric fibres. Scheme representability is an isomorphism with
the Yoneda presheaf of an actual scheme, for each member of the étale covering.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper, flat, finitely presented family with geometric fibres of dimension at most
one admits an étale scheme covering of its base on which its source is a scheme.
The predicate `IsProperCurveFamily` includes precisely these hypotheses. Its geometric
fibre dimension is the dimension of the existing point space, equivalently the supremum
of dimensions of affine étale charts; the empty fibre has dimension bottom.
Source: Stacks Project, moduli-curves.tex, Tag 0E6F, first assertion, with the convention
of section-stack-curves (blueprint: lem-sfb-curve-etale-scheme-cover).

Proof: (1) Apply [lem-sfb-curve-smooth-polarization-cover] to obtain a smooth surjective
scheme cover `U → T`, a scheme representing `X ×_T U`, and a relatively ample invertible
module on it. Its hypotheses are exactly the given proper curve-family conditions.
(2) Apply [lem-sfb-smooth-space-cover-etale-sections] to refine `U → T` by a jointly
surjective étale scheme covering `Tᵢ → T` with maps `Tᵢ → U` over `T`. This also covers
the empty base, using the empty covering.
(3) Form the scheme fibre products `Y ×_U Tᵢ` using [def-pc-fibre-product]. They represent
the algebraic-space pullbacks by [lem-trf-space-fibre-products-etale-covers]: on test
schemes the mutually inverse operations send `((x,u),tᵢ)` to `(x,tᵢ)` and `(x,tᵢ)` to
`((x,vᵢ(tᵢ)),tᵢ)`. They commute with pullback, so define inverse natural transformations,
which are the morphisms of [def-trf-algebraic-space]. No surjectivity of `X → T` is used. -/
theorem exists_etale_scheme_cover {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) (hf : IsProperCurveFamily X T f) :
    ∃ (I : Type u) (Tᵢ : I → Over S) (e : ∀ i : I, Tᵢ i ⟶ T),
      (∀ i : I, Etale (e i).left) ∧
      (∀ t : T.left, ∃ (i : I) (tᵢ : (Tᵢ i).left), (e i).left.base tᵢ = t) ∧
      ∀ i : I, ∃ Y : Over S,
        Nonempty (Limits.pullback f (yoneda.map (e i)) ≅ yoneda.obj Y) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
