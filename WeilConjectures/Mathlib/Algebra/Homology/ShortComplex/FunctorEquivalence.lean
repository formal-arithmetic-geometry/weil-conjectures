/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Exactness of short complexes in functor categories

A short complex in a functor category `J ⥤ A`, with `A` abelian, is exact as soon as it is exact
after evaluation at every object of `J`
(`CategoryTheory.ShortComplex.exact_of_forall_exact_map_evaluation`).
-/

@[expose] public section

namespace CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]

/-- A short complex in a functor category is exact if it is exact after evaluation
at every object. -/
lemma ShortComplex.exact_of_forall_exact_map_evaluation {J : Type*} [Category* J]
    (S : ShortComplex (J ⥤ A)) (h : ∀ j, (S.map ((evaluation J A).obj j)).Exact) :
    S.Exact := by
  rw [S.exact_iff_isZero_homology]
  exact Functor.isZero _ fun j => ((S.map _).exact_iff_isZero_homology.1 (h j)).of_iso
    (S.mapHomologyIso ((evaluation J A).obj j)).symm

end CategoryTheory
