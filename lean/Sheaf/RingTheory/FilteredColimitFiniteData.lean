/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
import Sheaf.Order.DirectedFiniteUpperBound

/-!
# Finite data and relations in a directed colimit of commutative rings

Source: the Weil conjectures blueprint, chapter `sec-nagata-compactification`, unit
`sk-prop-nagata-sketch-approximation`, node `lemma-nagata-filtered-colimit-finite-data`
(blueprint: lemma-nagata-filtered-colimit-finite-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Finitely many elements and ring equations in a directed colimit descend simultaneously
and remain true under every later transition. Ring expressions in the selected elements
are represented by multivariate polynomials over `ℤ`, which encode precisely the operations
of a commutative ring, including subtraction and integer constants.

Source: the Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-approximation`, lemma `lemma-nagata-filtered-colimit-finite-data`.
(blueprint: lemma-nagata-filtered-colimit-finite-data).

Proof for stage 3:
1. A nonempty directed preorder is filtered. By
   `lem-pc-filtered-colimit-commrings-elementwise` (1), choose a representative stage
   and a lift of each selected element.
2. Use directedness and `lemma-nagata-directed-finite-upper-bound` to move the finitely
   many lifts to a common stage.
3. Evaluate both polynomials of each equation on these lifts. Their images in the colimit
   agree by the selected equation. By `lem-pc-filtered-colimit-commrings-elementwise` (2),
   each equality becomes true at some later stage.
4. Apply `lemma-nagata-directed-finite-upper-bound` again to those finitely many witness
   stages and the common stage. Transporting the lifts there makes all equations true.
5. Ring homomorphisms commute with evaluation of integer polynomials, so every transition
   to a later stage preserves all these equations. -/
theorem exists_finite_data_stage {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ CommRingCat.{u}) (n m : ℕ)
    (x : Fin n → ↑(CategoryTheory.Limits.colimit F)) (p q : Fin m → MvPolynomial (Fin n) ℤ)
    (h : ∀ r : Fin m,
      (p r).eval₂ (Int.castRingHom ↑(CategoryTheory.Limits.colimit F)) x =
        (q r).eval₂ (Int.castRingHom ↑(CategoryTheory.Limits.colimit F)) x) :
    ∃ (i : I) (y : Fin n → F.obj i),
      (∀ a : Fin n, colimit.ι F i (y a) = x a) ∧
      (∀ r : Fin m,
        (p r).eval₂ (Int.castRingHom (F.obj i)) y =
          (q r).eval₂ (Int.castRingHom (F.obj i)) y) ∧
      (∀ (j : I) (hij : i ≤ j) (r : Fin m),
        (p r).eval₂ (Int.castRingHom (F.obj j))
            (fun a ↦ F.map (homOfLE hij) (y a)) =
          (q r).eval₂ (Int.castRingHom (F.obj j))
            (fun a ↦ F.map (homOfLE hij) (y a))) := by
  sorry

end CommRingCat
