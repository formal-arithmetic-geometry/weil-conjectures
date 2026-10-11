/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Filtered colimits of standard smooth algebras

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.3.5, Tag 07CI
(blueprint: lem-weil-pbc-colimit-standard-smooth-algebras).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- A filtered colimit of smooth `R`-algebras is a filtered colimit of standard smooth
`R`-algebras. `ObjectProperty.ind` supplies a small nonempty filtered index category,
a diagram of commutative `R`-algebras and a colimit presentation of `Λ`.
Algebras and index categories live in universe `max u v`, as in
lem-weil-pbc-algebra-colimit-fp-algebras-over-it, so that the index of step 4 (finitely
presented algebras over `R` with maps to `Λ`) is small.

Source: Stacks Project, Smoothing Ring Maps, Lemma 16.3.5, Tag 07CI
(blueprint: lem-weil-pbc-colimit-standard-smooth-algebras).

Proof:
1. Form the set of literal finite polynomial quotients with invertible Jacobian determinant.
   They are standard smooth (def-weil-pbc-standard-smooth-algebra), finitely presented
   (def-weil-pbc-finitely-presented-algebra), and represent all standard smooth algebras
   up to algebra isomorphism by transporting their standard smooth presentations.
2. A map from a finitely presented algebra `A` to `Λ` factors through a smooth stage `B`.
   Use def-weil-pbc-filtered-colimit-smooth-algebras and
   lem-weil-pbc-filtered-colimit-algebras-elementwise to regard the cocone as a ring colimit;
   apply lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit to a finite
   polynomial presentation of `A`, then transport back along the presentation isomorphism.
3. Apply lem-weil-pbc-smooth-retract-standard-smooth (Tag 07CH) to obtain `B → C → B`
   with composite the identity and `C` standard smooth. The composite `A → B → C → B → Λ`
   gives the required factorization through `C`, hence through a representative from step 1.
4. Apply lem-weil-pbc-factorization-criterion-filtered-colimit (Tag 07C3) to that set of
   finitely presented algebras and these factorizations. It produces a filtered diagram
   of standard smooth algebras with colimit `Λ`, as in def-weil-pbc-category-colimit. -/
theorem ind_isStandardSmooth_of_ind_smooth
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (h : ObjectProperty.ind.{max u v} (fun B : CommAlgCat.{max u v} R ↦ Smooth R B) Λ) :
    ObjectProperty.ind.{max u v} (fun C : CommAlgCat.{max u v} R ↦ IsStandardSmooth R C)
      Λ := by
  sorry

end Algebra
