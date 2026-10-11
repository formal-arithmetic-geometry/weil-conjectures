/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation

/-!
# Filtered colimits from a factorization criterion

Source: Stacks Project, Algebra, Lemma 10.127.4, Tag 07C3, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-factorization-criterion-filtered-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- If every map from a finitely presented `R`-algebra to `Λ` factors through a member
of a set `E` of finitely presented `R`-algebras, then `Λ` is a filtered colimit of
members of `E`. The natural transformation `ι` gives the compatible coprojections,
and `IsColimit` gives their universal property. The index category is small, in the
universe `max u v` of the algebras (as in lem-weil-pbc-algebra-colimit-fp-algebras-over-it);
no smallness assumption on `E` is needed, since finitely presented algebras have only a
small set of isomorphism classes.

Source: Stacks Project, Algebra, Lemma 10.127.4, Tag 07C3, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-factorization-criterion-filtered-colimit).

Proof:
1. Choose `E' ⊆ E` containing exactly one member of each isomorphism class meeting `E`;
   it is small since finitely presented algebras form a small set of isomorphism classes.
   Let `P₀` be the set of quotients of finite polynomial algebras by finitely generated
   ideals, and put `P = P₀ ∪ E'`. Every finitely presented algebra is isomorphic to a
   member of `P`. The category `I` of pairs `(A, α : A → Λ)` with `A ∈ P` is small,
   filtered, and its forgetful diagram has colimit `Λ`, by
   lem-weil-pbc-algebra-colimit-fp-algebras-over-it (Tag 0BUF), with colimit understood
   as in def-weil-pbc-category-colimit.
2. Let `J` be the full subcategory on pairs `(B, γ)` with `B ∈ E'`. The hypothesis
   factors every `α` as `β ≫ γ` through a member of `E`, and composing with an
   isomorphism onto a member of `E'` gives an arrow from every object of `I` to an
   object of `J`. This subcategory is small.
3. Apply lem-weil-pbc-colimit-initial-full-subcategory to `Iᵒᵖ` and `Jᵒᵖ` (Tags 0BUC
   and 04E7). It says that `J` is filtered and the colimit of the restricted diagram
   maps isomorphically to `Λ`, compatibly with its coprojections.
4. Transport the colimit cocone along this isomorphism. Explicitly, if `L → Λ` is
   the comparison isomorphism and `L → M` the unique map to another cocone, composing
   with its inverse gives the unique map `Λ → M`. Thus the maps `γ` make `Λ` a
   colimit of the diagram of members of `E`, as in def-weil-pbc-category-colimit. -/
theorem exists_filtered_colimit_of_factorization
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (E : Set (CommAlgCat.{max u v} R))
    (hfp : ∀ B ∈ E, Algebra.FinitePresentation R B)
    (hfactor : ∀ (A : CommAlgCat.{max u v} R), Algebra.FinitePresentation R A →
      ∀ (α : A ⟶ Λ), ∃ (B : CommAlgCat.{max u v} R), B ∈ E ∧
        ∃ (β : A ⟶ B) (γ : B ⟶ Λ), β ≫ γ = α) :
    ∃ (J : Type (max u v)) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ CommAlgCat.{max u v} R) (ι : D ⟶ (Functor.const J).obj Λ),
      (∀ j : J, D.obj j ∈ E) ∧ Nonempty (IsColimit (Cocone.mk Λ ι)) := by
  sorry

end CommAlgCat
