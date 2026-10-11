/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.ConeCategory

/-!
# An algebra as the filtered colimit of finitely presented algebras over it

Source: Stacks Project, Tag 0BUF, Lemma `lemma-ring-colimit-fp-category` and its footnote
(blueprint: lem-weil-pbc-algebra-colimit-fp-algebras-over-it).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- Stacks Project, Tag 0BUF, Lemma `lemma-ring-colimit-fp-category`, with a set `P`
containing a representative of each finitely presented algebra.
(blueprint: lem-weil-pbc-algebra-colimit-fp-algebras-over-it).

`P` being a set of algebras of `CommAlgCat.{max u v} R` is `ObjectProperty.Small.{max u v} P`;
`I` being small is `Small.{max u v}` of its objects (its hom types lie in `Type (max u v)`).

The full subcategory `P.FullSubcategory` has all algebra maps between its objects, so
`CostructuredArrow P.ι Λ` has precisely the pairs `(A, α : A ⟶ Λ)` and commuting triangles
in the statement. The cocone below has vertex `Λ` and component `α` at `(A, α)`.

Proof from the node, following Tag 0BUF:
1. The objects `(A, α)` have `A` in the set `P` and `α` in the set of algebra maps
   `A ⟶ Λ`, so they form a set and the index is small. A representative of `R`, with its
   structure map to `Λ`, makes the index nonempty
   (def-weil-pbc-finitely-presented-algebra).
2. Representatives of tensor products give common upper bounds
   (lem-weil-pbc-tensor-product-finitely-presented-algebras).
3. Quotient the target of parallel arrows by the differences of their values on finitely
   many algebra generators, then choose its representative. This equalizes the arrows
   (lem-weil-pbc-finite-presentation-quotient-fg-ideal). Thus the index is filtered.
4. Take the colimit `B` in commutative algebras and its canonical map `B ⟶ Λ`
   (lem-weil-pbc-commutative-algebras-colimits-exist, def-weil-pbc-category-colimit).
5. Each element of `Λ` is hit using evaluation from `R[x]`, so this map is surjective.
6. Represent an element of its kernel in a stage, then quotient that stage by the
   principal ideal it generates. This kills the element in the colimit
   (lem-weil-pbc-filtered-colimit-algebras-elementwise,
   lem-weil-pbc-finite-presentation-quotient-fg-ideal), proving injectivity.
7. Transport the colimit property along the resulting algebra isomorphism `B ≅ Λ`
   (def-weil-pbc-category-colimit). -/
theorem isFiltered_and_isColimit_finitelyPresentedAlgebras
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (P : ObjectProperty (CommAlgCat.{max u v} R)) [ObjectProperty.Small.{max u v} P]
    (hfp : ∀ A : CommAlgCat.{max u v} R, P A → Algebra.FinitePresentation R A)
    (hrep : ∀ A : CommAlgCat.{max u v} R, Algebra.FinitePresentation R A →
      ∃ B : P.FullSubcategory, Nonempty (A ≅ B.obj)) :
    Small.{max u v} (CostructuredArrow P.ι Λ) ∧ IsFiltered (CostructuredArrow P.ι Λ) ∧
      Nonempty (IsColimit (Cocone.fromCostructuredArrow P.ι
        (𝟭 (CostructuredArrow P.ι Λ)))) := by
  sorry

end CommAlgCat
