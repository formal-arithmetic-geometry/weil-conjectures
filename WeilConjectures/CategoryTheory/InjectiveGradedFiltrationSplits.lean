/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Compatible splitting of a filtration with injective graded pieces

Source: Stacks Project, Derived Categories, Tag 05TP, lemma-filtered-injective;
the fixed interval and graded-piece identifications are its displayed split filtration.
(blueprint: lem-trf-injective-graded-filtration-splits).
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.FilteredObject

open Limits

/-- A finite decreasing filtration with injective graded pieces has a simultaneous
splitting identifying every filtration subobject with the corresponding tail biproduct.

Source: Stacks Project, Derived Categories, Tag 05TP, lemma-filtered-injective.
(blueprint: lem-trf-injective-graded-filtration-splits).

Proof: take J_n = gr^n I. Extend the quotient map F^n I → J_n along the mono
F^n I → I, using injectivity, to a coordinate f_n : I → J_n. Its restriction to
F^p I vanishes for p > n, since that inclusion factors through F^(n+1) I and the
quotient kills this next step. For each p let B_p be the biproduct over p ≤ n in
[a,b], and define α_p : F^p I → B_p by these restricted coordinates. The coordinate
vanishing proves compatibility with the inclusions of successive steps and tails.
Projection onto J_p makes 0 → B_(p+1) → B_p → J_p → 0 split short exact.
Descending induction proves α_p invertible for a ≤ p ≤ b+1: at b+1 both objects
are zero; the induction step compares the filtration's short exact sequence with
this split sequence, with identity on J_p, and applies the short five lemma.
The map β : I → B with coordinates f_n is invertible at p=a, because F^a I=I
and B_a=B. For all p the coordinate calculation gives inclusion ≫ β = α_p ≫
tail-inclusion. For a ≤ p ≤ b+1 invertibility of α_p yields equality of image
subobjects. For p<a both subobjects are top by decreasingness and F^a I=I.
For p>b+1 both are zero by decreasingness and F^(b+1) I=0, and the tail is empty.
Take θ to be β as an isomorphism and take identity isomorphisms J_n ≅ gr^n I. -/
theorem injective_graded_filtration_splits
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : FilteredObject C) (a b : ℤ) (hab : a ≤ b)
    (ha : X.filtration.F a = ⊤) (hb : X.filtration.F (b + 1) = ⊥)
    (hgr : ∀ n : Set.Icc a b, Injective (X.filtration.gradedPiece n.1)) :
    ∃ J : Set.Icc a b → C,
      (∀ n : Set.Icc a b, Injective (J n)) ∧
      (∀ n : Set.Icc a b, Nonempty (J n ≅ X.filtration.gradedPiece n.1)) ∧
      ∃ θ : X.obj ≅ @biproduct _ C _ _ J (HasBiproduct.of_hasProduct J),
        ∀ p : ℤ, (Subobject.map θ.hom).obj (X.filtration.F p) =
          imageSubobject (@biproduct.fromSubtype _ C _ _ J
            (HasBiproduct.of_hasProduct J) (fun n : Set.Icc a b ↦ p ≤ n.1)
            (HasBiproduct.of_hasProduct _)) := by
  sorry

end CategoryTheory.FilteredObject
