/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Yoneda

/-!
# Local separatedness of algebraic-space morphisms

Source: Stacks Project, Morphisms of Algebraic Spaces, Tags 03KL, 03KQ and 03KY;
Schemes, Tag 01KJ (blueprint: lem-sfb-space-locally-separated-base-change).

Local separatedness is written with the existing scheme-test predicate
`IsRepresentableWith`: every scheme base change of the relative diagonal is an immersion.
The fibre products and diagonals below are in presheaves, hence are the underlying
presheaves of the sheaf fibre products of the algebraic spaces. Their algebraicity is
supplied by `fibreProduct_isAlgebraicSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Local separatedness is stable under arbitrary algebraic-space base change.
Source: Stacks, Tag 03KL (blueprint: lem-sfb-space-locally-separated-base-change).
Proof: put X' = X ×_Y Y', P = X ×_Y X and P' = X' ×_{Y'} X'. The map P' → P
forgets Y'. The fibre product P' ×_P X has sections ((x₁,y'),(x₂,y'),x) with
x₁ = x = x₂. Sending such a section to (x,y') is a natural bijection with X',
whose inverse sends (x,y') to ((x,y'),(x,y'),x). Thus the new diagonal is the
base change of the old one. The sheaf products are algebraic spaces by
lem-trf-space-fibre-products-etale-covers. Immersion is stable under arbitrary
algebraic-space base change by lem-sfb-space-immersion-affine-tests, so the new
relative diagonal is representable by immersions as required. -/
theorem locallySeparated_baseChange {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal f.hom.hom)) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal (pullback.snd f.hom.hom g.hom.hom)) := by
  sorry

/-- Locally separated algebraic-space morphisms compose.
Source: Stacks, Tag 03KQ (blueprint: lem-sfb-space-locally-separated-base-change).
Proof: first, representable immersions compose. On a scheme test T → C of
A → B → C, represent T ×_C B by W and W ×_B A by V. Forgetting the middle
coordinate gives h_V = h_T ×_C A, with inverse inserting the image in B.
The projection V → W → T is an immersion by clause (e) of
lem-weil-pbc-proper-fp-permanence. For the asserted composition, put
P = X ×_Y X and Q = X ×_Z X. Pull back the diagonal of g along the map
Q → Y ×_Z Y induced by f on both factors. Its sections are (x₁,x₂,y) with
f(x₁) = y = f(x₂); forgetting y identifies this pullback with P, with inverse
inserting f(x₁). Thus P → Q is an immersion by
lem-sfb-space-immersion-affine-tests. Composing it with the immersion diagonal
X → P gives the diagonal X → Q of f ≫ g. All products are algebraic spaces
by lem-trf-space-fibre-products-etale-covers. -/
theorem locallySeparated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal f.hom.hom))
    (hg : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal g.hom.hom)) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal (f.hom.hom ≫ g.hom.hom)) := by
  sorry

/-- Every scheme morphism, viewed through its functor of points, is locally separated.
Source: Stacks, Tags 03KY and 01KJ
(blueprint: lem-sfb-space-locally-separated-base-change).
Proof: the scheme fibre-product universal property (def-pc-fibre-product) identifies
h_{X ×_Y X} with h_X ×_{h_Y} h_X, compatibly with diagonals. By
lem-weil-pbc-diagonal-immersion the scheme diagonal is an immersion. Yoneda
(lem-pc-yoneda) identifies each scheme test of its functor of points with an actual
scheme map into X ×_Y X. The tested pullback is the scheme fibre product and
its projection is an immersion by clause (1) of
lem-weil-pbc-immersion-base-change-lft. These pullback squares are exactly the
witnesses required by IsRepresentableWith. No separatedness of either scheme
or of its structure morphism to S is needed. -/
theorem locallySeparated_yonedaMap {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (pullback.diagonal (yoneda.map f)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
