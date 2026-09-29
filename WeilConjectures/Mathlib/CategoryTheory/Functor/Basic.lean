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

## Implementation notes

Unlike `Nat.iterate`, whose definitional unfolding is `f^[n + 1] = f^[n] ∘ f`, the recursion
here applies the new copy of `G` last: `G.iterate (n + 1) = G.iterate n ⋙ G`, that is
`Gⁿ⁺¹ = G ∘ Gⁿ`. This makes iterated structure maps of algebras, such as
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate`, definitional. Accordingly, the
definitional equation is `Functor.iterate_succ'`, matching `Function.iterate_succ'`, and the
other order is the lemma `Functor.iterate_succ`, matching `Function.iterate_succ`. Since
composition of functors is definitionally associative, both hold as equalities of functors.
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

variable (G : C ⥤ C)

@[simp]
lemma iterate_zero : G.iterate 0 = 𝟭 C :=
  rfl

lemma iterate_succ' (n : ℕ) : G.iterate (n + 1) = G.iterate n ⋙ G :=
  rfl

@[simp]
lemma iterate_one : G.iterate 1 = G :=
  rfl

lemma iterate_succ (n : ℕ) : G.iterate (n + 1) = G ⋙ G.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.iterate (n + 1) ⋙ G = G ⋙ G.iterate n ⋙ G
    rw [ih]
    rfl

lemma iterate_add (m n : ℕ) : G.iterate (m + n) = G.iterate m ⋙ G.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.iterate (m + n) ⋙ G = G.iterate m ⋙ G.iterate n ⋙ G
    rw [ih]
    rfl

end CategoryTheory.Functor
