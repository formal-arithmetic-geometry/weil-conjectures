/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Kaplansky direct-summand decomposition

Source: Stacks Project, Algebra, Theorem 058X (theorem-kaplansky-direct-sum), lines 20471–20570.
(blueprint: lem-trf-projective-kaplansky-direct-summand)
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

namespace Module

open Classical in
/-- A direct summand of a direct sum of countably generated modules is a direct sum of
countably generated modules.
Source: Stacks Project, Algebra, Theorem 058X (theorem-kaplansky-direct-sum).
(blueprint: lem-trf-projective-kaplansky-direct-summand)

Proof:
1. Transport along `hM` and identify `P` with the image of `a`, whose inverse there is `b`.
   The endomorphism `e = a.comp b` is idempotent with image `P`; the coordinate submodule
   `M_A` consists of families supported in `A`, with coordinate projection `π_A`.
2. By `lem-trf-countable-coordinate-closure`, for each `j` choose a countable set `D_j`
   containing `j` such that `e` preserves `M_{D_j}`. Then `1 - e` preserves it too.
3. Well-order `J` with order type `κ`. Starting with `A₀ = ∅`, take unions at limits and
   adjoin `D_j` for the least omitted index at each successor (or adjoin nothing if exhausted).
   Each increment is countable, and `e` preserves every `M_{A_α}`. At a limit, finite support
   lies in one earlier stage, giving continuity of the coordinate filtration.
4. Ordinal induction shows that `A_α` contains all indices below `α`: at a successor the
   current index is already included or is the least omitted one, and at a limit use the
   union. Thus `A_κ = J`, even if some coordinate modules are zero.
5. Set `P_α = P ∩ M_{A_α} = e(M_{A_α})`. These submodules have endpoints zero and `P` and
   are continuous at limits. The map `e ∘ π_{A_α}` retracts `P_{α+1}` onto `P_α`, because
   it fixes every element of `P_α`; no commutation of the two projections is required.
6. Let `B_α = A_{α+1} \ A_α`. The images of countable generating sets for `N_j`, for
   `j ∈ B_α`, generate `M_{B_α}` and form a countable set. Sending `z` to the class of
   `e(z)` surjects onto `P_{α+1}/P_α`: split the coordinates of a representative into the
   old coordinates and `B_α`. The quotient is therefore countably generated, including
   the empty-increment case. Quotients use `def-weil-pbc-quotient-module`.
7. Apply `lem-trf-split-transfinite-module-filtration` to obtain the direct sum of these
   successor quotients and transport back to the original `P`. If `J` is empty, `κ = 0`
   and `P` is the zero module.

The index type `I` can be chosen in the universe of `J` by reindexing the ordinal stages
along its well-order. The quotient factors are in the universe of `P`. All input module
universes are independent; no cardinality restriction on the ring or modules is used.
-/
theorem exists_directSum_countablyGenerated_of_split
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (J : Type w) (N : J → Type x) [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (hN : ∀ j, ∃ s : Set (N j), s.Countable ∧ Submodule.span R s = ⊤)
    (hM : Nonempty ((DirectSum J N) ≃ₗ[R] M))
    (P : Type y) [AddCommGroup P] [Module R P]
    (a : P →ₗ[R] M) (b : M →ₗ[R] P) (hba : b.comp a = LinearMap.id) :
    ∃ (I : Type w) (Q : I → Type y) (_ : ∀ i, AddCommGroup (Q i))
      (_ : ∀ i, Module R (Q i)),
      (∀ i, ∃ s : Set (Q i), s.Countable ∧ Submodule.span R s = ⊤) ∧
      Nonempty ((DirectSum I Q) ≃ₗ[R] P) := by
  sorry

end Module
