/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.CategoryTheory.Triangulated.ProZeroMiddle

/-!
# Uniformly bounded derived towers with pro-zero cohomology

Source: Stacks Project, Derived Categories, Tag 0G3B, specialized to zero-valued systems
(blueprint: lem-weil-pbc-bounded-derived-tower-pro-zero).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- A uniformly bounded tower whose cohomology towers are pro-zero is itself pro-zero.
The index `n : ℕ` represents the paper's index `n + 1`; the functor laws encode identity
and composition of all transition maps.

Source: Stacks Project, Derived Categories, Tag 0G3B
(blueprint: lem-weil-pbc-bounded-derived-tower-pro-zero).

Proof plan: for a fixed target index choose a later index dominating the finitely many
indices killing the cohomology maps in degrees `[a, b]`; outside this interval cohomology
is zero. Apply the functorial canonical truncation triangle at `a`
(lem-sf-derived-truncation-triangle). Its lower term is `H^a(X)[-a]`, since lower
cohomology vanishes, and its transitions are the shifted cohomology maps. The upper
terms have cohomology in `[a + 1, b]`. Induct on `b - a`; for `a = b` use the
single-degree identification (lem-sf-derived-concentrated-single). In the induction
step both outer towers are pro-zero, so the zero-valued two-out-of-three lemma
(lem-weil-pbc-essentially-constant-zero-triangle, Tag 0G3A) makes the middle tower
pro-zero. -/
theorem tower_proZero_of_bounded_homology_proZero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : ℕᵒᵖ ⥤ DerivedCategory A) (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
      IsZero ((homologyFunctor A q).obj (X.obj (op n))))
    (hpro : ∀ (q : ℤ) (n : ℕ), ∃ (k : ℕ) (h : n ≤ k),
      (homologyFunctor A q).map (X.map (homOfLE h).op) = 0) :
    ∀ (n : ℕ), ∃ (k : ℕ) (h : n ≤ k), X.map (homOfLE h).op = 0 := by
  sorry

end DerivedCategory
