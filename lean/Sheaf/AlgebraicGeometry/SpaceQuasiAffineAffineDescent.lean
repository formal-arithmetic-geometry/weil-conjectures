/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Quasi-affine scheme representability descends over a faithfully flat affine base

Source: Stacks Project, Spaces Descent, Tag 0423, lemma-descending-property-quasi-affine,
affine flat-surjective reduction; Morphisms of Spaces, Tag 03WL, definition-quasi-affine
(blueprint: lem-sfb-space-quasi-affine-affine-descent).

Scheme representability is expressed by an isomorphism of presheaves on `Over S`.
The presheaf pullback is also the underlying presheaf of the sheaf fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- If the base change of an algebraic space along a flat surjective map of affine
`S`-schemes is represented by a quasi-affine scheme, so is the original space.
Here `Scheme.IsQuasiAffine` includes quasi-compactness, and its canonical map to the
spectrum of global sections is an open immersion. No representability, separation or
finiteness condition is imposed on the map `f`.

Source: Stacks Project, Spaces Descent, Tag 0423, lemma-descending-property-quasi-affine,
affine flat-surjective reduction; Morphisms of Spaces, Tag 03WL, definition-quasi-affine
(blueprint: lem-sfb-space-quasi-affine-affine-descent).

Proof:
1. The morphism `p.left` between affine schemes is affine by
   [pqf-lem-affine-local-target], hence quasi-compact by
   [lem-weil-pbc-affine-morphism-permanence]. Together with flatness and surjectivity,
   this makes its singleton family fpqc [def-weil-pbc-fpqc-covering]. For a quasi-affine
   scheme `P` representing the pullback, its map to affine `V.left` is quasi-affine by
   [lem-a1-quasi-affine-target-locality].
2. Over `V ×_U V`, both pullbacks of `P` represent triples `(x,v0,v1)` with matching
   images in `U`. Retaining the triple and changing the distinguished `P`-coordinate
   from `(x,v0)` to `(x,v1)` gives the canonical isomorphism. Over the triple product,
   both successive transport and direct transport send `(x,v0)` to `(x,v2)`. This is
   the cocycle of [def-pd-descent-datum], using the fibre-product description of
   [lem-trf-space-fibre-products-etale-covers].
3. Apply [lem-trf-quasi-affine-fpqc-effective-descent] to obtain a scheme `Y` over `U`
   and an isomorphism `Y ×_U V ≅ P` inducing that datum. The morphism `Y → U` is
   quasi-affine by [lem-sfb-scheme-quasi-affine-fpqc-descent]. Since `U` is affine,
   `Y` itself is quasi-affine by [def-nagata-quasi-affine-morphism].
4. For each `U`-scheme `T`, its pullback `T_V → T` is fpqc by
   [lem-galois-fpqc-covering-base-change]. A map `T → Y` gives locally a section of
   `X` via `Y ×_U V ≅ P`. The datum fixes its `X`-coordinate on overlaps, so
   [lem-a1-algebraic-space-fpqc-sheaf] glues it uniquely to `T → X`. The result is
   over `U` by uniqueness in [lem-weil-pbc-fpqc-representable-descent] with target `U`.
5. Conversely, a section `T → X` over `U` gives a map `T_V → P`, hence `T_V → Y`.
   Compatibility with the same datum makes its two restrictions agree. Apply
   [lem-weil-pbc-fpqc-representable-descent] to glue a unique `T → Y`, over `U` by
   uniqueness with target `U`. The two constructions are inverse locally by the
   representing isomorphism and globally by the uniqueness clauses for `X` and `Y`.
6. These bijections commute with restriction because their local formulas do and
   gluing is unique. For an arbitrary `S`-scheme `T`, decompose the maps by their
   composite `T → U`. The bijections for each composite give an isomorphism of
   presheaves `h_Y ≅ X`, hence the desired representation [def-trf-algebraic-space]. -/
theorem exists_quasiAffine_representation_of_flat_surjective_affine_baseChange
    {S : Scheme.{u}} (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (p : V ⟶ U) [Flat p.left] [Surjective p.left]
    (X : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj U)
    (h : ∃ P : Over S, P.left.IsQuasiAffine ∧
      Nonempty (yoneda.obj P ≅ Limits.pullback f (yoneda.map p))) :
    ∃ Y : Over S, Y.left.IsQuasiAffine ∧ Nonempty (yoneda.obj Y ≅ X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
