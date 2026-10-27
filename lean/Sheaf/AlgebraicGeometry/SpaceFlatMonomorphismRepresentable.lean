/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Flat monomorphisms of algebraic spaces are representable

Source: Stacks Project, More on Morphisms of Spaces, Tag 0B8A (lemma-flat-case),
David Rydh (blueprint: lem-sfb-space-flat-monomorphism-representable).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat algebraic-space morphism injective on sections of every test scheme is
representable by schemes, without a finiteness hypothesis.

Source: Stacks Project, More on Morphisms of Spaces, Tag 0B8A (lemma-flat-case),
David Rydh (blueprint: lem-sfb-space-flat-monomorphism-representable).

Proof:
1. For an arbitrary scheme test `h_T → Y`, put `Z = X ×_Y h_T`.
   By lem-trf-space-fibre-products-etale-covers this is an algebraic space, and by
   lem-sfb-space-flat-proper-fp-locality its projection to `T` is flat. On each test
   scheme, two pairs with the same `T` component have equal `X` components by monomorphy.
   Cover `T` by affine opens. Their inverse images cover `Z`; once they are schemes,
   lem-sfb-space-largest-schematic-open and lem-a1-space-point-open-calculus imply
   that the largest schematic open is all of `Z`. Thus assume `T = Spec B`.
2. By lem-a1-space-affine-atlas-open-cover, cover `Z` by open subspaces `W` with affine
   surjective étale atlases. Their point spaces are quasi-compact, as continuous images
   of affine schemes (lem-a1-space-point-open-calculus). The map `q : W → Spec B`
   remains flat and monic; its diagonal is an isomorphism, hence quasi-compact.
   The target is quasi-separated by lem-weil-pbc-affine-morphism-permanence, so
   lem-sfb-space-qcqs-permanence makes `q` quasi-compact. As in step 1, it suffices
   to show that each `W` is a scheme.
3. Apply lem-sfb-space-schemehood-local-ring-test to `q`. For a point `w` above `t`,
   set `A = O_(Spec B,t)` and `P = W ×_(Spec B) Spec A`. The projection `r` is flat
   and quasi-compact by lem-sfb-space-flat-proper-fp-locality and
   lem-sfb-space-quasicompact-affine-tests, and remains monic by the pair calculation.
   A field-valued representative of `w` factors through `Spec A` and gives a point of
   `P` over its closed point. It remains to show each such `P` is a scheme.
4. By lem-sfb-space-quasicompact-affine-tests choose a quasi-compact scheme atlas of
   `P`; a finite affine open cover and lem-weil-pbc-affine-morphism-permanence give
   an affine surjective étale atlas `u : U → P`. Its composite `v = r ∘ u` is flat by
   the chart test def-sfb-space-morphism-properties. Surjectivity on points of `u`
   follows from lem-a1-space-point-open-calculus. Thus some point of `U` maps to the
   closed point of `Spec A`. Every point of a local spectrum generalizes that point;
   lem-weil-pbc-flat-generalizations-lift makes `v`, hence `r`, surjective.
5. The singleton affine flat surjection `v` is an fpqc covering
   (def-weil-pbc-fpqc-covering): each affine open of `Spec A` is a finite union of
   standard opens, whose inverse images are affine standard opens of `U` and cover it
   surjectively. Form `P ×_(Spec A) U` by lem-trf-space-fibre-products-etale-covers.
   Monomorphy of `r` gives an inverse to its projection to `U`, on sections sending
   `y` to `(u(y), y)`. Thus the projection is an isomorphism, hence an open immersion.
   By lem-sfb-space-fpqc-open-immersion-descent, `r` identifies `P` with an open
   subscheme of `Spec A`; surjectivity makes this the whole of `Spec A`.
6. The local-ring test makes every `W` a scheme. The largest schematic opens in steps
   2 and 1 then show that `Z` is a scheme. Since the scheme test was arbitrary, `f`
   is representable. Quasi-compactness was needed only for the auxiliary pieces `W`.
-/
theorem flat_monomorphism_representable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : MapIsFlat f)
    (hmono : ∀ H : Over S, Function.Injective (f.hom.hom.app (op H))) :
    IsRepresentable f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
