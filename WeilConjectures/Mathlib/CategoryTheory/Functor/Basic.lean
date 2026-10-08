/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Iterating an endofunctor

For an endofunctor `G : C ⥤ C` and a natural number `n`, this file defines the `n`-fold
composition `G.iterate n : C ⥤ C`.

## Main definitions

- `CategoryTheory.Functor.iterate`: the `n`-fold composition of an endofunctor, with
  `G.iterate 0 = 𝟭 C` and `G.iterate (n + 1) = G.iterate n ⋙ G`.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold composition of an endofunctor, with `G.iterate 0 = 𝟭 C` and
`G.iterate (n + 1) = G.iterate n ⋙ G`. -/
def iterate (G : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => G.iterate n ⋙ G

@[simp]
lemma iterate_zero (G : C ⥤ C) : G.iterate 0 = 𝟭 C :=
  rfl

@[simp]
lemma iterate_succ (G : C ⥤ C) (n : ℕ) : G.iterate (n + 1) = G.iterate n ⋙ G :=
  rfl

end CategoryTheory.Functor
