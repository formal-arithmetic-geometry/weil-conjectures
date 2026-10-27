module

public import Sheaf.RingTheory.CoordinateSubmodule
public import Mathlib.Data.Set.Countable
public import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.RelClasses

/-!
# Invariant transfinite coordinate filtrations

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20500–20533 and 20555–20565.
(blueprint: lem-trf-invariant-coordinate-transfinite-filtration)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace DirectSum

/-- Prescribed countable invariant coordinate blocks give an exhaustive continuous
transfinite coordinate filtration, with the least omitted coordinate added at each successor.

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20500–20533 and 20555–20565.
(blueprint: lem-trf-invariant-coordinate-transfinite-filtration)

Proof:
1. By `lem-weil-pbc-well-ordering-theorem`, well-order `J`; by
   `lem-trf-well-order-ordinal-enumeration` enumerate it by `η` below its order type `κ`.
   This also treats the empty index set, with `κ = 0`.
2. Apply `lem-weil-pbc-transfinite-recursion` to subsets of `J`: start with the empty set,
   take unions at nonzero limits, and at a successor adjoin the specified block of the
   least omitted coordinate, keeping the set unchanged once it is all of `J`.
   Surjectivity of the enumeration gives a missing index whenever needed. Transfinite
   induction gives monotonicity because successor stages contain their predecessors
   and limit stages are unions.
3. From `def-trf-coordinate-submodule` and `def-weil-pbc-direct-sum-modules`, the
   coordinate submodule of a union of two subsets is the sum of their coordinate
   submodules: split a finite-support family into coordinates in the first set and
   its complement in the second. Linearity thus preserves invariance at successors,
   using the prescribed block's invariance; the zero submodule is invariant initially.
4. At a nonzero limit, every finite support lies in one earlier stage: take the maximum
   of the finitely many witness stages, or stage zero for empty support. This proves
   equality with the union of earlier coordinate submodules, and also invariance at
   limits. Together with step 3, transfinite induction gives invariance at every stage.
5. Inductively, all coordinates enumerated before `α` lie in `A α`. At a successor,
   the current enumerated coordinate is either already present, or it is the least
   omitted one and belongs to its own block. At limits use the union and the successor
   of each earlier index. Surjectivity gives `A κ = Set.univ`, even for zero summands.
6. Each successor difference is empty or contained in one prescribed countable block,
   hence countable. The coordinate submodules of the empty and full sets are zero
   and the full module. No countable generation of any summand has been used.
-/
theorem exists_invariant_coordinate_transfinite_filtration
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (f : (DirectSum J N) →ₗ[R] DirectSum J N) (D : J → Set J)
    (hD_countable : ∀ j, (D j).Countable) (hD_self : ∀ j, j ∈ D j)
    (hD_invariant : ∀ j x, x ∈ coordinateSubmodule R J N (D j) →
      f x ∈ coordinateSubmodule R J N (D j)) :
    ∃ (κ : Ordinal.{v}) (η : Set.Iio κ ≃ J) (A : Set.Iic κ → Set J),
      Monotone A ∧
      A ⟨0, (bot_le : (0 : Ordinal.{v}) ≤ κ)⟩ = ∅ ∧
      A ⟨κ, le_refl κ⟩ = Set.univ ∧
      (∀ μ : Set.Iic κ, Order.IsSuccLimit μ.val →
        A μ = ⋃ (β : Set.Iic κ) (_ : β < μ), A β) ∧
      (∀ (α : Ordinal.{v}) (hα : α < κ),
        (A ⟨α, le_of_lt hα⟩ = Set.univ →
          A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ = A ⟨α, le_of_lt hα⟩) ∧
        (A ⟨α, le_of_lt hα⟩ ≠ Set.univ →
          ∃ γ : Set.Iio κ, η γ ∉ A ⟨α, le_of_lt hα⟩ ∧
            (∀ δ : Set.Iio κ, δ < γ → η δ ∈ A ⟨α, le_of_lt hα⟩) ∧
            A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ =
              A ⟨α, le_of_lt hα⟩ ∪ D (η γ))) ∧
      (∀ (α : Ordinal.{v}) (hα : α < κ),
        (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩).Countable) ∧
      (∀ (α : Set.Iic κ) (β : Set.Iio κ), β.val < α.val → η β ∈ A α) ∧
      coordinateSubmodule R J N (A ⟨0, (bot_le : (0 : Ordinal.{v}) ≤ κ)⟩) = ⊥ ∧
      coordinateSubmodule R J N (A ⟨κ, le_refl κ⟩) = ⊤ ∧
      (∀ (α : Set.Iic κ) x, x ∈ coordinateSubmodule R J N (A α) →
        f x ∈ coordinateSubmodule R J N (A α)) ∧
      (∀ μ : Set.Iic κ, Order.IsSuccLimit μ.val →
        (coordinateSubmodule R J N (A μ) : Set (DirectSum J N)) =
          ⋃ (β : Set.Iic κ) (_ : β < μ),
            (coordinateSubmodule R J N (A β) : Set (DirectSum J N))) := by
  sorry

end DirectSum
