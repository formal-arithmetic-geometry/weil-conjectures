/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Data.Finset.Order

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
  classical
  have map_eval {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
      (P : MvPolynomial (Fin n) ℤ) (z : Fin n → R) :
      φ (P.eval₂ (Int.castRingHom R) z) =
        P.eval₂ (Int.castRingHom S) (fun a ↦ φ (z a)) := by
    rw [MvPolynomial.hom_eval₂, RingHom.eq_intCast' (φ.comp (Int.castRingHom R))]
  choose stage lift hlift using fun a ↦ Concrete.colimit_exists_rep F (x a)
  obtain ⟨i, hi⟩ := (Finset.univ.image stage).exists_le
  let e (a : Fin n) : stage a ⟶ i :=
    homOfLE (hi _ (Finset.mem_image_of_mem stage (Finset.mem_univ a)))
  let y (a : Fin n) : F.obj i := F.map (e a) (lift a)
  have hy (a : Fin n) : colimit.ι F i (y a) = x a :=
    (ConcreteCategory.congr_hom (colimit.w F (e a)) (lift a)).trans (hlift a)
  have heq (r : Fin m) :
      colimit.ι F i ((p r).eval₂ (Int.castRingHom (F.obj i)) y) =
        colimit.ι F i ((q r).eval₂ (Int.castRingHom (F.obj i)) y) := by
    simpa only [map_eval, hy] using h r
  have eventual (r : Fin m) : ∃ (j : I) (f : i ⟶ j),
      F.map f ((p r).eval₂ (Int.castRingHom (F.obj i)) y) =
        F.map f ((q r).eval₂ (Int.castRingHom (F.obj i)) y) := by
    obtain ⟨j, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq F _ _ (heq r)
    exact ⟨j, f, (Subsingleton.elim g f) ▸ hfg⟩
  choose j f hj using eventual
  obtain ⟨k, hk⟩ := (insert i (Finset.univ.image j)).exists_le
  let e₀ : i ⟶ k := homOfLE (hk i (Finset.mem_insert_self _ _))
  let e₁ (r : Fin m) : j r ⟶ k :=
    homOfLE (hk _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem j (Finset.mem_univ r))))
  let z (a : Fin n) : F.obj k := F.map e₀ (y a)
  have hz (r : Fin m) :
      (p r).eval₂ (Int.castRingHom (F.obj k)) z =
        (q r).eval₂ (Int.castRingHom (F.obj k)) z := by
    have hr := congrArg (F.map (e₁ r)) (hj r)
    have hcomp : f r ≫ e₁ r = e₀ := Subsingleton.elim _ _
    have hmap (v : F.obj i) : F.map (e₁ r) (F.map (f r) v) = F.map e₀ v := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    simpa only [hmap, map_eval] using hr
  refine ⟨k, z, ?_, hz, ?_⟩
  · intro a
    exact (ConcreteCategory.congr_hom (colimit.w F e₀) (y a)).trans (hy a)
  · intro l hkl r
    exact (map_eval (F.map (homOfLE hkl)).hom (p r) z).symm.trans
      ((congrArg (F.map (homOfLE hkl)) (hz r)).trans
        (map_eval (F.map (homOfLE hkl)).hom (q r) z))

end CommRingCat
