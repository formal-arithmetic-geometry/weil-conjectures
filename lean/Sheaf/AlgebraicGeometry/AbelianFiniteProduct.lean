/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.Dimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField

/-!
# Finite products and the zero abelian variety

Source: Stacks Project, varieties.tex, Tag 0B2M, lemma-dimension-product-locally-algebraic;
Groupoid Schemes Tags 03RO, 0B7Q and 0BFC.
(blueprint: lem-sfb-abelian-finite-product)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

/-- A finite product of abelian varieties over a field is an abelian variety of additive
dimension. The projection homomorphism conditions specify the componentwise group operations.

Source: Stacks Project, varieties.tex, Tag 0B2M, lemma-dimension-product-locally-algebraic;
Groupoid Schemes Tags 03RO, 0B7Q and 0BFC.
(blueprint: lem-sfb-abelian-finite-product)

Proof:
1. The empty product is `Spec k` by the terminal universal property. Its unique multiplication,
   inverse and identity satisfy the group diagrams (def-sc-group-scheme). Its identity structure
   map is proper and smooth and its space is a singleton (def-sc-abelian-variety). Its local ring
   is `k`, whose Krull dimension is zero (def-pc-dimension).
2. For two factors use def-pc-fibre-product to construct multiplication, inverse and identity
   coordinatewise. Projection to either factor verifies all group diagrams. The projection to
   the second factor is proper and smooth by lem-pc-proper-base-change. Composition preserves
   properness (lem-weil-pbc-proper-composition) and smoothness (lem-trf-smooth-composition).
3. By lem-sc-abelian-variety-characterization, the first factor is geometrically integral and
   hence geometrically connected (def-pc-geometrically-irreducible, def-pc-integral-scheme).
   The connected-component bijection of
   lem-weil-pbc-geometrically-connected-product-components makes the product connected, since
   the second factor is nonempty and connected. Thus the product is an abelian variety.
4. Induct on the cardinality of the finite set, identifying the successor product with the
   binary product by def-pc-fibre-product. Properness includes finite type, and both factors
   are nonempty, so lem-sfb-scheme-product-dimension proves the dimension sum at each step.
5. For the converse, lem-pc-algebraic-dim-zero-affine-finite makes the zero-dimensional abelian
   variety affine. By lem-sc-abelian-variety-characterization it is geometrically integral.
   Clause (2) of lem-pc-h0-proper-variety identifies its global sections with `k` as a `k`-algebra.
   The affine criterion lem-sc-affine-global-sections-iso makes the structure map an isomorphism.
6. The structure map to the terminal scheme preserves multiplication by uniqueness of maps to
   that scheme. Its inverse is the identity section; composing its multiplication diagram with
   the structure isomorphism proves that it too preserves multiplication (def-sc-group-scheme).
-/
theorem finite_product_isAbelianVariety_and_dim
    {k : Type u} [Field k] {J : Type v} [Fintype J]
    (A : J → Over (Spec (CommRingCat.of k)))
    [∀ j, GrpObj (A j)] [∀ j, IsAbelianVariety (A j)] :
    ∃ (_ : GrpObj (piObj A)),
      (∀ j, IsMonHom (Pi.π A j)) ∧ IsAbelianVariety (piObj A) ∧
        (piObj A).left.dim = ∑ j, (A j).left.dim := by
  sorry

/-- The empty product of abelian varieties is the trivial group scheme `Spec k`.

Source: Stacks Project, groupoids.tex, Tag 03RO, definition-abelian-variety;
the terminal universal property of the empty product.
(blueprint: lem-sfb-abelian-finite-product)

Proof: Step 1 of the node identifies the empty product in `k`-schemes with `Spec k`.
All group operations and maps to this terminal object are unique, so the canonical scheme
isomorphism and its inverse preserve multiplication (def-sc-group-scheme).
-/
theorem empty_product_abelian_is_trivial
    {k : Type u} [Field k] {J : Type v} [IsEmpty J]
    (A : J → Over (Spec (CommRingCat.of k))) :
    ∃ (_ : GrpObj (piObj A)) (e : piObj A ≅ 𝟙_ (Over (Spec (CommRingCat.of k)))),
      IsMonHom e.hom ∧ IsMonHom e.inv := by
  sorry

/-- Every zero-dimensional abelian variety over a field is the trivial group scheme.

Source: Stacks Project, varieties.tex, Tag 06LH, lemma-algebraic-scheme-dim-0;
Tag 0BUG, lemma-proper-geometrically-reduced-global-sections; Tag 04L2,
lemma-regular-functions-proper-variety; Groupoid Schemes Tag 03RO.
(blueprint: lem-sfb-abelian-finite-product)

Proof: By properness (def-weil-proper-morphism), the scheme has finite type, so
lem-pc-algebraic-dim-zero-affine-finite makes it affine. Its geometric integrality follows from
lem-sc-abelian-variety-characterization. Clause (2) of lem-pc-h0-proper-variety identifies its
coordinate algebra with `k`; lem-sc-affine-global-sections-iso makes its structure map an
isomorphism. Uniqueness of maps to the terminal scheme proves that this isomorphism is a
homomorphism; its inverse is the identity section and is a homomorphism by cancellation
(def-sc-group-scheme), as in steps 5 and 6 of the node.
-/
theorem zero_dimensional_abelian_is_trivial
    {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety A] (h : A.left.dim = 0) :
    ∃ e : A ≅ 𝟙_ (Over (Spec (CommRingCat.of k))),
      IsMonHom e.hom ∧ IsMonHom e.inv := by
  sorry

end AlgebraicGeometry
