/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Elementary changes between generating tuples over a local ring

Source: Stacks Project, Algebra, Tags 00DV (`lemma-NAK`) and 00E9
(`lemma-characterize-local-ring`); the agent-formulated generating-tuple consequence
used in the local-ring reduction of `lem-pur-frame-independence.proof.md`
(blueprint: lem-pur-local-generating-tuples).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Module

/-- Any two equal-length generating tuples over a commutative local ring differ by
finitely many unit scalings, swaps and shears, with their corresponding matrix product.

Source: Stacks Project, Algebra, Tags 00DV (`lemma-NAK`) and 00E9
(`lemma-characterize-local-ring`), agent-formulated consequence
(blueprint: lem-pur-local-generating-tuples).

Proof, following the six steps of the node:
1. Induct on `c`, uniformly for all finite modules over the fixed ring. If `c = 0`,
   generation forces the module to be zero; take no operations and the identity matrix.
   If the module is zero at any other length, the two tuples are identical as well.
2. Otherwise, Nakayama with the zero submodule (`lem-weil-pbc-nakayama-local-generators`,
   `IsLocalRing.map_mkQ_eq_top`) shows that the quotient by the maximal-ideal multiple
   is nonzero. Some target generator survives there; permute it to the first position.
3. Express this generator as a linear combination of the source tuple. One coefficient
   is outside the maximal ideal, hence a unit (`lem-weil-pbc-local-ring-unit-criterion`,
   `IsLocalRing.notMem_maximalIdeal`). Swap its source entry to the first position,
   scale it by that unit, and add the other coefficient multiples to the first entry.
   This gives a tuple whose first entry agrees with the permuted target. Each operation
   is invertible: inverse unit, the same swap, or the shear with negative coefficient.
4. Quotient by the submodule spanned by that common first entry. Both tails generate
   the quotient, making it finite (`def-weil-finitely-generated-module`). Apply induction
   to these tails of length `c - 1`; for `c = 1` this is the empty quotient-tail case.
5. Lift the tail operations to the module while fixing the first entry. The quotient
   map respects unit scaling, swaps and shears, so induction on the finite operation list
   gives the prescribed quotient tail. The differences from the target are now multiples
   of the fixed first entry. Correct them with shears from that entry to each tail entry,
   and undo the original target permutation. All concatenated operation lists are finite.
6. Record each operation's matrix: a unit diagonal matrix, a swap permutation matrix,
   or `I + a E i j` for distinct indices. Their inverses are the inverse-unit diagonal,
   the same swap, and `I - a E i j`, since `E i j` squares to zero. For chronological
   matrices `A 0, ..., A (s - 1)`, their action on column tuples is the reverse product.
   The converse reads such a product from right to left. At length zero this is the
   empty product. A finitely generated ideal is a specialization of the module statement. -/
theorem exists_elementary_generating_tuple_change
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (c : ℕ) (f g : Fin c → M)
    (hf : Submodule.span R (Set.range f) = ⊤)
    (hg : Submodule.span R (Set.range g) = ⊤) :
    ∃ (s : ℕ) (x : ℕ → Fin c → M)
      (A : Fin s → Matrix.GeneralLinearGroup (Fin c) R),
      x 0 = f ∧ x s = g ∧
      (∀ (t : ℕ) (ht : t < s),
        (∃ (i : Fin c) (u : Rˣ),
          (∀ k, x (t + 1) k = if k = i then (u : R) • x t i else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then (u : R) * z i else z k)) ∨
        (∃ (i j : Fin c), i ≠ j ∧
          (∀ k, x (t + 1) k =
            if k = i then x t j else if k = j then x t i else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then z j else if k = j then z i else z k)) ∨
        (∃ (i j : Fin c) (a : R), i ≠ j ∧
          (∀ k, x (t + 1) k = if k = i then x t i + a • x t j else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then z i + a * z j else z k))) ∧
      ∃ (P : Matrix.GeneralLinearGroup (Fin c) R),
        (∀ i, g i = ∑ j : Fin c, (P : Matrix (Fin c) (Fin c) R) i j • f j) ∧
        P = (List.ofFn A).reverse.prod := by
  sorry

end Module
