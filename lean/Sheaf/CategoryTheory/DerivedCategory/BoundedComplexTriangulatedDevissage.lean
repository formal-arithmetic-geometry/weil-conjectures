/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Bounded complexes belong to triangulated subcategories containing their terms

Source: literature/stacks-project/derived.tex, Tag 0FCP, lemma-K-bounded-derived
(blueprint: lem-weil-pbc-bounded-complex-triangulated-devissage).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
A bounded complex belongs to a strictly full triangulated subcategory containing each
of its terms in degree zero.

Source: literature/stacks-project/derived.tex, Tag 0FCP, lemma-K-bounded-derived, proof:
the displayed stupid-truncation triangles and finite induction
(blueprint: lem-weil-pbc-bounded-complex-triangulated-devissage).

Proof:
1. If `a > b`, the support condition makes every term zero. The complex is isomorphic
   to zero, as is its image under `Q`, so it belongs to `S`. Otherwise let `T n` be the
   stupid tail with terms `K.X q` for `n ≤ q` and zero below. The support bounds identify
   `T a` with `K` and `T (b + 1)` with zero (def-weil-abstract-derived-category).
2. For `a ≤ n ≤ b`, let `E n` be `K.X n` placed in degree `n`. The termwise inclusion
   `T (n + 1) → T n` and projection `T n → E n` commute with differentials. In degree
   `n` their sequence is `0 → K.X n → K.X n`, in higher degrees it is the identity
   followed by zero, and below `n` it is zero. Thus it is degreewise short exact
   (def-sp-abelian).
3. By lem-weil-pbc-complex-ses-triangle this sequence gives a distinguished triangle
   `Q(T (n + 1)) → Q(T n) → Q(E n) → Q(T (n + 1))[1]`.
4. The shift convention gives `E n ≅ (K.X n)[0][-n]`. As `Q` commutes with shifts,
   the term hypothesis and shift/isomorphism closure put `Q(E n)` in `S`
   (def-weil-abstract-derived-category).
5. For `N = b - a + 1`, induct on `k = 0,...,N` to put `Q(T (b + 1 - k))` in `S`.
   The base case is zero. At each step put `n = b - k` and rotate the triangle twice:
   its vertices are `Q(E n)`, `Q(T (n + 1))[1]`, `Q(T n)[1]`. The first two belong
   to `S`; third-vertex closure and shifting back give `Q(T n)` in `S`
   (def-weil-triangulated-category). The endpoint and `T a ≅ K` give the result.
-/
theorem bounded_complex_mem_triangulated
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ObjectProperty (DerivedCategory C)) [S.IsTriangulated]
    [S.IsClosedUnderIsomorphisms] (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ q : ℤ, q < a ∨ b < q → IsZero (K.X q))
    (hS : ∀ q : ℤ, a ≤ q → q ≤ b →
      S ((DerivedCategory.singleFunctor C 0).obj (K.X q))) :
    S (DerivedCategory.Q.obj K) := by
  sorry

end CategoryTheory
