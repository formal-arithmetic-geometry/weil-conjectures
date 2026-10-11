/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Final

/-!
# Finite initial truncation of the simplicial indexing category

Source: Stacks Project, Tag 017K, proof, and Tag 002R
(blueprint: lem-weil-pbc-simplicial-index-finite-initial).

`S.Elements` is the opposite of the category of simplices in the node: a morphism
`(n,s) ⟶ (m,t)` lies over `[m] ⟶ [n]` and satisfies `S(φ)(s) = t`.
The degree predicate selects the full subcategory directly, without a new definition.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

/-- Stacks Project, Tag 017K, proof; limit comparison by Tag 002R.
(blueprint: lem-weil-pbc-simplicial-index-finite-initial)

Proof:
1. The truncated category has finitely many objects, the union of the finite `S_n`
   for `n ≤ 2 m₀`, and finite hom sets, subsets of the finite monotone-map sets.
2. By lem-weil-pbc-simplicial-set-nondegenerate-decomposition, every simplex is the
   degeneracy of a nondegenerate simplex of degree at most `m₀`. This supplies a
   morphism from an object of the truncation to each object of `S.Elements`.
3. Two monotone maps `[k] → [n]`, `[k] → [n']` with `n,n' ≤ m₀` each have at most
   `m₀` ascents. If `k > 2 m₀`, among the first `2 m₀ + 1` adjacent pairs there
   is one on which both maps are constant.
4. By lem-weil-pbc-simplex-degeneracy-factorization the maps factor through that
   elementary degeneracy. By lem-weil-pbc-simplicial-degeneracy-injective their
   associated lower-dimensional simplices agree. Induction on `k` supplies a common
   factor of degree at most `2 m₀` for the two maps.
5. For arbitrary endpoints in the truncation, first decompose both into simplices
   of degree at most `m₀`, then apply step 4. In the node's category this gives
   `y → u ← a → u' ← y'`; in `S.Elements` all four arrows are reversed.
   The morphisms to the fixed object commute and extend the two given morphisms.
   A sequence on `ℕ` records its first `2 r + 1` objects; its unused tail can be constant.
6. Steps 2 and 5 establish initiality. By lem-weil-pbc-initial-functor-limit (002R),
   restriction preserves and detects existence of limits, and the canonical comparison
   morphism is an isomorphism whenever the limits exist. -/
theorem simplicialIndex_finite_initial (S : SSet.{u}) [S.Finite]
    (hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌)))
    (hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌)))
    (m₀ : ℕ) (hdegenerate : ∀ n : ℕ, m₀ < n → ∀ s : S.obj (op ⦋n⦌),
      s ∈ S.degenerate n) :
    Finite (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)) ∧
    (∀ y y' : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)), Finite (y ⟶ y')) ∧
    (∀ z : S.Elements, ∃ y : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)), Nonempty (y.obj ⟶ z)) ∧
    (∀ (z : S.Elements) (y y' : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)))
      (α : y.obj ⟶ z) (α' : y'.obj ⟶ z),
      ∃ (r : ℕ) (ys : ℕ → (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀))) (a : ∀ i : ℕ, (ys i).obj ⟶ z),
        ys 0 = y ∧ ys (2 * r) = y' ∧ HEq (a 0) α ∧ HEq (a (2 * r)) α' ∧
        ∀ i : ℕ, i < r →
          ∃ (f : (ys (2 * i + 1)).obj ⟶ (ys (2 * i)).obj)
            (g : (ys (2 * i + 1)).obj ⟶ (ys (2 * i + 2)).obj),
            f ≫ a (2 * i) = a (2 * i + 1) ∧
            g ≫ a (2 * i + 2) = a (2 * i + 1)) ∧
    (ObjectProperty.ι
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)).Initial ∧
    (∀ (C : Type v) [Category.{w} C] (D : S.Elements ⥤ C),
      HasLimit D ↔ HasLimit ((ObjectProperty.ι
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)) ⋙ D)) ∧
    (∀ (C : Type v) [Category.{w} C] (D : S.Elements ⥤ C)
      [HasLimit D] [HasLimit ((ObjectProperty.ι
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)) ⋙ D)],
      IsIso (limit.pre D (ObjectProperty.ι
      (fun x : S.Elements => x.fst.unop.len ≤ 2 * m₀)))) := sorry

end SSet
