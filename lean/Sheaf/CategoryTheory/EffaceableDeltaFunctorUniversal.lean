/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.DeltaFunctor

/-!
# Effaceable delta-functors are universal

Source: Stacks Project, Homology, Lemma 010T (lemma-efface-implies-universal)
(blueprint: lem-weil-pbc-effaceable-delta-functor-universal).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

/-- An effaceable cohomological delta-functor is universal.

This is Grothendieck's effacement criterion, Stacks Project, Homology, Lemma 010T.
The proof constructs the extension inductively using the cokernel description supplied
by an effacing short exact sequence; independence of choices, naturality, and
compatibility with connecting morphisms follow from comparison via biproducts and
pushouts, and uniqueness follows by cancellation of the resulting epimorphisms.
(blueprint: lem-weil-pbc-effaceable-delta-functor-universal) -/
theorem effaceable_deltaFunctor_isUniversal
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ (n : ℕ), 0 < n → ∀ (X : A),
      ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F.F n).map u = 0) :
    F.IsUniversal := by
  sorry

end CategoryTheory
