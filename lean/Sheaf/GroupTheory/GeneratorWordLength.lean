module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Length in an indexed alphabet of monoid elements

Source: Cashen, Notes on Coxeter groups (31 October 2023), Chapter 4, Lemma 4.0.5,
minimal tuples in an alphabet, used without a presentation hypothesis.
(blueprint: def-sfb-generator-word-length)
-/

@[expose] public section

universe u v

namespace Monoid

/-- Minimum length of a positive word representing `g` in the indexed alphabet `t`.
The empty word has product `1`. The value is `0` if no such word exists; when a word
exists, `Nat.sInf_def` identifies this with the attained minimum of its possible lengths.
Source: Cashen, Notes on Coxeter groups, Chapter 4, Lemma 4.0.5, minimal tuples.
(blueprint: def-sfb-generator-word-length) -/
noncomputable def generatorWordLength {G : Type u} [Monoid G] {I : Type v}
    (t : I → G) (g : G) : ℕ :=
  sInf {n : ℕ | ∃ A : List I, A.length = n ∧ (A.map t).prod = g}

end Monoid
