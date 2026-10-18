/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# Dold--Kan normalization equivalence

Source: Stacks Tag 019G, theorem-dold-kan; blueprint:
`lem-cbc-dold-kan-normalization-equivalence`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Abelian.DoldKan

/-- (blueprint: lem-cbc-dold-kan-normalization-equivalence)
The normalized Moore complex functor gives the Dold--Kan equivalence between
simplicial objects and nonnegative chain complexes in an abelian category.  The
equivalence carries its inverse and the unit and counit natural isomorphisms,
which are the `N`, `Γ`, `NΓ ≅ id`, and `ΓN ≅ id` data in the node statement.
Source: Stacks Tag 019G, theorem-dold-kan; Mathlib
`CategoryTheory.Abelian.DoldKan.equivalence`.
-/
noncomputable def doldKanNormalizationEquivalence
    (A : Type u) [Category.{v, u} A] [Abelian A] :
    SimplicialObject A ≌ ChainComplex A ℕ :=
  CategoryTheory.Abelian.DoldKan.equivalence

end CategoryTheory.Abelian.DoldKan

