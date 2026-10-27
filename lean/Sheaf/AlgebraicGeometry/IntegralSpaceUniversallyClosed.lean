/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover

/-! # Integral morphisms of algebraic spaces are affine and universally closed

Source: Stacks Project, Morphisms of Spaces, Tag 0415, implication (1) to (2),
with the scheme-test criterion of Tag 03IT
(blueprint: lem-sfb-space-integral-universally-closed).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral morphism of algebraic spaces is affine and universally closed.
The integral hypothesis uses actual scheme-valued pullback squares for every scheme test.
The conclusion uses the existing affine and universally closed morphism predicates.
Source: Stacks Project, Morphisms of Spaces, Tag 0415, implication (1) to (2), and
Tag 03IT, proof of (3) to (4)
(blueprint: lem-sfb-space-integral-universally-closed).

Proof:
1. For every scheme T mapping to X, the hypothesis represents Y ×_X T by a scheme
   integral over T. By [def-weil-finite-integral-morphism], its projection is affine.
   For affine T its source is affine, giving MapIsAffine f; conversely the affine-test
   definition gives affine scheme base changes over arbitrary T by gluing over affine opens.
2. Fix any algebraic space X' mapping to X and put Z = Y ×_X X'. These products exist
   by [lem-trf-space-fibre-products-etale-covers]. For every representable etale scheme
   test T → X', the scheme V = Y ×_X T identifies with Z ×_{X'} T. Its map h : V → T
   is integral, hence universally closed by [pqf-lem-integral-univclosed]. The point map
   of q : V → Z is continuous by [lem-a1-space-affine-etale-cover].
3. For a closed C in |Z|, the inverse image of its image in |X'| along |T| → |X'|
   equals the image under |h| of the inverse image of C under |q|. One inclusion is
   commutativity. For the other, points with equal images have field representatives
   agreeing after a common field extension, by [def-a1-algebraic-space-point-classes].
   The pullback universal property gives a point of V projecting to both representatives.
   This does not assert that the underlying topological square is cartesian.
4. The inverse image under |q| is closed, and its image under |h| is closed. Thus every
   etale scheme test has closed inverse image of the image of C. The final topology
   [def-a1-space-point-topology], applied to complements, makes that image closed in
   |X'|. This proves MapIsUniversallyClosed f, with no extra finiteness, surjectivity,
   quasi-compactness or Noetherian assumption. -/
theorem affine_and_universallyClosed_of_integral
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) f.hom.hom) :
    MapIsAffine f ∧ MapIsUniversallyClosed f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
