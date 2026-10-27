/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Replacing a finite block in an arbitrary module basis

Source: Stacks Project, Algebra, Tag 0592, lemma-projective-freeness-criteria,
second paragraph of the proof (blueprint: lem-trf-finite-block-basis-replacement).
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace Module.Basis

/-- Replacing finitely many basis vectors by vectors with an invertible matrix of
selected coordinates and arbitrary complementary tails gives an automorphism, a
basis with the original index type, and a basis of a complementary free summand.

Source: Stacks Project, Algebra, Tag 0592, lemma-projective-freeness-criteria,
second paragraph of the proof (blueprint: lem-trf-finite-block-basis-replacement).

Proof: (1) Write each vector in its unique finite basis expansion. Define linear
maps U and W on the basis by U(e_i) = y_i, W(e_i) = sum_j V_ij (e_j - t_j),
and let both maps fix every complementary basis vector. They therefore fix the
complementary span pointwise. (2) On the selected vectors the composite U W has
coefficient matrix V B, so it is the identity; it also fixes the complement.
Finite basis expansions show U W is the identity everywhere. (3) Similarly W U
has selected part B V and the tails cancel, so W U is the identity everywhere.
These formulas include the empty selected block. (4) Expand W(x) and apply U to
obtain an expansion of x in the replacement family. Applying W to two such
expansions proves uniqueness, so this family is a basis with the original indices.
(5) Restrict its selected vectors to their span to obtain the finite basis there.
Splitting the replacement coordinates into selected and complementary coordinates
gives x = g + t; uniqueness of the same coordinates gives uniqueness of the pair.
-/
theorem finite_block_replacement
    {R : Type u} {F : Type v} {ι : Type w}
    [CommRing R] [AddCommGroup F] [Module R F]
    (b : Module.Basis ι R F) (n : ℕ) (e : Fin n ↪ ι)
    (y t : Fin n → F) (B V : Matrix (Fin n) (Fin n) R)
    (ht : ∀ i, t i ∈ Submodule.span R (b '' (Set.range e)ᶜ))
    (hy : ∀ i, y i = (∑ j : Fin n, B i j • b (e j)) + t i)
    (hBV : B * V = 1) (hVB : V * B = 1) :
    (∃ U : F ≃ₗ[R] F,
      (∀ i, U (b (e i)) = y i) ∧
      ∀ j, j ∉ Set.range e → U (b j) = b j) ∧
    (∃ b' : Module.Basis ι R F,
      (∀ i, b' (e i) = y i) ∧
      ∀ j, j ∉ Set.range e → b' j = b j) ∧
    (∃ c : Module.Basis (Fin n) R (Submodule.span R (Set.range y)),
      ∀ i, (c i : F) = y i) ∧
    ∀ x : F, ∃! p : (Submodule.span R (Set.range y)) ×
        (Submodule.span R (b '' (Set.range e)ᶜ)),
      x = (p.1 : F) + (p.2 : F) := by
  sorry

end Module.Basis

end
