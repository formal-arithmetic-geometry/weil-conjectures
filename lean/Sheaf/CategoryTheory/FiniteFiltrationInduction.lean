/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.CategoryTheory.Filtration

/-!
# Finite filtration induction

Source: the blueprint of the Weil conjectures, chapter `sec-proper-base-change`,
unit `sk-thm-properbasechange`, node `lem-sp-finite-filtration-induction`
(blueprint: lem-sp-finite-filtration-induction); Stacks Project, Homology,
Definition 0121 (`definition-filtered`), the paragraph defining `gr` before Lemma 05SP,
and Lemma 0127 (`lemma-characterize-strict`).
-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

/-- The map induced by a filtered morphism on its `p`-th filtration steps.
Source: Stacks Project, Homology, Definition 0121 (3) and the diagram in Lemma 0127.
The factorization is unique because the target subobject inclusion is monic.
(blueprint: lem-sp-finite-filtration-induction) -/
noncomputable def restriction {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    (A.filtration.step p : C) ⟶ (B.filtration.step p : C) :=
  Classical.choose (f.preserves p)

/-- Existence of the map induced on the graded pieces by a filtered morphism.
Source: Stacks Project, Homology, the paragraph defining `gr` before Lemma 05SP
and the commutative diagram in Lemma 0127.

Proof (the quotient-map construction in Step 1 of the node): compose each chosen
restriction with its target inclusion. The defining equalities from `f.preserves`
and the inclusions of successive steps show that the two composites from the
`(p + 1)`-st source step to the `p`-th target step become equal after the monic
inclusion into `B.obj`. Cancel that inclusion. Thus `restriction f p` carries the
source inclusion into the target inclusion, which the target cokernel kills.
Apply the universal property of the source cokernel to obtain `g` and its equation.
The filtration steps and graded pieces are those of `def-sp-filtration`.
(blueprint: lem-sp-finite-filtration-induction). -/
theorem exists_gradedMap (A B : FilteredObject C) (f : Hom A B) (p : ℤ) :
    ∃ g : A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p,
      cokernel.π (Subobject.ofLE (A.filtration.step (p + 1))
        (A.filtration.step p) (A.filtration.antitone_step (by omega))) ≫ g =
        restriction f p ≫ cokernel.π (Subobject.ofLE (B.filtration.step (p + 1))
          (B.filtration.step p) (B.filtration.antitone_step (by omega))) := by
  sorry

/-- The map induced by a filtered morphism on its graded pieces.
Source: Stacks Project, Homology, the paragraph defining `gr` before Lemma 05SP
and the commutative diagram in Lemma 0127. This is the unique map commuting with
the cokernel projections, chosen from `exists_gradedMap`.
(blueprint: lem-sp-finite-filtration-induction) -/
noncomputable def gradedMap {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p :=
  Classical.choose (exists_gradedMap A B f p)

/-- A morphism inducing isomorphisms on all graded pieces of finite filtrations
is an isomorphism, and all induced maps on filtration steps are isomorphisms.

Source: Stacks Project, Homology, Lemma 0127 (`lemma-characterize-strict`),
the descending-induction argument in the proof of (3) implies (2).

Proof:
1. Use `def-sp-filtration` to choose common bounds `n ≤ m`: decrease the two
   lower bounds to their minimum and increase the upper bounds to their maximum
   (and, if necessary, increase `m` to `n`). Steps with `p ≤ n` are whole objects;
   steps with `p ≥ m` are zero. Uniqueness of factorization through each monic
   target inclusion makes the restrictions commute with consecutive inclusions.
   The cokernel universal property then defines the graded maps. For every `p`,
   these form a commutative diagram of the short exact sequences
   `0 → F^(p+1) → F^p → gr^p → 0` and their counterparts for `B`.
2. For `p ≥ m` the restriction is a map between zero objects, hence an isomorphism.
   Descend through the finitely many integers from `m` to `n`. At each step the
   left arrow is an isomorphism by induction and the right arrow by `hgraded`.
   The short five lemma (`lem-weil-pbc-short-five-lemma`, realized by
   `CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃`) makes the middle
   restriction an isomorphism. For `p < n`, both steps are whole objects, so the
   same conclusion follows by their canonical identifications with the `n`-th steps.
3. At `n`, both inclusions into the underlying objects are isomorphisms. Their
   commutative square expresses `f.hom` as a composite of the restriction at `n`
   with these isomorphisms. Therefore `f.hom` is an isomorphism. All restrictions
   being isomorphisms says `f(F^p A) = F^p B`, so the map is strict as asserted.
(blueprint: lem-sp-finite-filtration-induction) -/
theorem finite_filtration_induction (A B : FilteredObject C) (f : Hom A B)
    (hA : A.filtration.IsFinite) (hB : B.filtration.IsFinite)
    (hgraded : ∀ p : ℤ, IsIso (gradedMap f p)) :
    IsIso f.hom ∧ ∀ p : ℤ, IsIso (restriction f p) := by
  sorry

end FilteredObject

end CategoryTheory
