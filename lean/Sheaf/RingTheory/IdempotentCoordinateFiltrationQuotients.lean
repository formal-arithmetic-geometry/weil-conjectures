/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.RingTheory.CoordinateSubmodule
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# The coordinate filtration on the image of an idempotent

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20489–20533.
(blueprint: lem-trf-idempotent-coordinate-filtration-quotients)
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace DirectSum

/-- The intersection of the image of `e` with the coordinates in `A`.

Source: Stacks Project, Algebra, Tag 058X, induced filtration on the summand.
(blueprint: lem-trf-idempotent-coordinate-filtration-quotients)
-/
noncomputable abbrev idempotentCoordinatePiece
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (e : DirectSum J N →ₗ[R] DirectSum J N) (A : Set J) :
    Submodule R (DirectSum J N) :=
  e.range ⊓ coordinateSubmodule R J N A

/-- The quotient of the image piece on `B` by the image piece on `A`, viewed inside `B`.
For `A ⊆ B` this is precisely `P_B / P_A`, using Mathlib's submodule quotient.

Source: Stacks Project, Algebra, Tag 058X, successive quotients on the summand.
(blueprint: lem-trf-idempotent-coordinate-filtration-quotients)
-/
noncomputable abbrev idempotentCoordinateQuotient
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (e : DirectSum J N →ₗ[R] DirectSum J N) (A B : Set J) :=
  idempotentCoordinatePiece R J N e B ⧸
    (idempotentCoordinatePiece R J N e A).comap
      (idempotentCoordinatePiece R J N e B).subtype

open Classical in
/-- An invariant continuous coordinate filtration induces a continuous split filtration
on the image of an idempotent, with the specified countable generators of each quotient.
The existential maps below are determined by their displayed formulas.

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20489–20533.
(blueprint: lem-trf-idempotent-coordinate-filtration-quotients)

Proof:
1. Idempotence fixes every element of `e.range`. Invariance gives
   `e(M_A) ⊆ e.range ∩ M_A`; conversely an element of this intersection is its own image.
2. Coordinate containment gives monotonicity. The empty and full coordinate sets give
   the zero piece and `e.range`, respectively, by `def-trf-coordinate-submodule`.
3. At a nonzero limit, the support of a direct-sum element is finite
   (`def-weil-pbc-direct-sum-modules`). Choose an earlier stage for each support index,
   then take their finite maximum, or zero for empty support. This proves continuity.
4. Mathlib's `DFinsupp.filterLinearMap` erases the coordinates outside `A_α`.
   Invariance puts `e` of this projection in `P_α`. It fixes `P_α` by step 1, so the
   displayed linear map retracts the inclusion. No commutation of the two maps is used.
5. Define `q(z)` as the class of `e(z)`, using `def-weil-pbc-quotient-module`.
   For a representative `p ∈ P_{α+1}`, split `p = a + z` into its old coordinates
   and its new coordinates. Then `p = e(p) = e(a) + e(z)`, with `e(a) ∈ P_α`.
   This proves surjectivity of the specified map from the new coordinate submodule.
6. Expand the finitely many nonzero coordinates of `z` as finite linear combinations
   of the chosen `G_j`. Linearity and step 5 show that their images generate the quotient.
7. Inject the countable index set and each `G_j` into the naturals. Encode `(j,g)`
   by `2^(b(j)) * (2*c_j(g)+1)`. This is injective. Give each distinct image its least
   representing code to prove countability. If the increment is empty, the image set
   is empty and the quotient is zero. Steps 6 and 7 give countable generation.
-/
theorem idempotent_coordinate_filtration_quotients
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (hN : ∀ j, ∃ G : Set (N j), G.Countable ∧ Submodule.span R G = ⊤)
    (e : DirectSum J N →ₗ[R] DirectSum J N) (he : e.comp e = e)
    (κ : Ordinal.{t}) (A : Set.Iic κ → Set J)
    (hA : Monotone A)
    (hzero : A ⟨0, (bot_le : (0 : Ordinal.{t}) ≤ κ)⟩ = ∅) (htop : A ⟨κ, le_refl κ⟩ = Set.univ)
    (hlimit : ∀ μ : Set.Iic κ, Order.IsSuccLimit μ.val →
      A μ = ⋃ (β : Set.Iic κ) (_ : β < μ), A β)
    (hinvariant : ∀ (α : Set.Iic κ) x, x ∈ coordinateSubmodule R J N (A α) →
      e x ∈ coordinateSubmodule R J N (A α))
    (hcountable : ∀ (α : Ordinal.{t}) (hα : α < κ),
      (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩).Countable) :
    (∀ α : Set.Iic κ, idempotentCoordinatePiece R J N e (A α) =
      (coordinateSubmodule R J N (A α)).map e) ∧
    Monotone (fun α : Set.Iic κ => idempotentCoordinatePiece R J N e (A α)) ∧
    idempotentCoordinatePiece R J N e (A ⟨0, (bot_le : (0 : Ordinal.{t}) ≤ κ)⟩) = ⊥ ∧
    idempotentCoordinatePiece R J N e (A ⟨κ, le_refl κ⟩) = e.range ∧
    (∀ μ : Set.Iic κ, Order.IsSuccLimit μ.val →
      (idempotentCoordinatePiece R J N e (A μ) : Set (DirectSum J N)) =
        ⋃ (β : Set.Iic κ) (_ : β < μ),
          (idempotentCoordinatePiece R J N e (A β) : Set (DirectSum J N))) ∧
    (∀ (α : Ordinal.{t}) (hα : α < κ),
      ∃ (hle : idempotentCoordinatePiece R J N e (A ⟨α, le_of_lt hα⟩) ≤
          idempotentCoordinatePiece R J N e
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩))
        (r : idempotentCoordinatePiece R J N e
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩) →ₗ[R]
          idempotentCoordinatePiece R J N e (A ⟨α, le_of_lt hα⟩))
        (q : coordinateSubmodule R J N
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩) →ₗ[R]
          idempotentCoordinateQuotient R J N e (A ⟨α, le_of_lt hα⟩)
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩)),
        (∀ p, (r p : DirectSum J N) =
          e (DFinsupp.filterLinearMap R N (fun j => j ∈ A ⟨α, le_of_lt hα⟩)
            (p : DirectSum J N))) ∧
        r.comp (Submodule.inclusion hle) = LinearMap.id ∧
        (∀ z : coordinateSubmodule R J N
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩),
          ∃ p : idempotentCoordinatePiece R J N e
              (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩),
          (p : DirectSum J N) = e (z : DirectSum J N) ∧
          q z = ((idempotentCoordinatePiece R J N e (A ⟨α, le_of_lt hα⟩)).comap
            (idempotentCoordinatePiece R J N e
              (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩)).subtype).mkQ p) ∧
        Function.Surjective q ∧
        (∀ G : ∀ j : J, Set (N j),
          (∀ j ∈ A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩,
            (G j).Countable ∧ Submodule.span R (G j) = ⊤) →
          (q '' {z | ∃ j ∈
              A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩,
            ∃ g ∈ G j, (z : DirectSum J N) = lof R J N j g}).Countable ∧
          Submodule.span R (q '' {z | ∃ j ∈
              A ⟨Order.succ α, Order.succ_le_of_lt hα⟩ \ A ⟨α, le_of_lt hα⟩,
            ∃ g ∈ G j, (z : DirectSum J N) = lof R J N j g}) = ⊤) ∧
        (∃ S : Set (idempotentCoordinateQuotient R J N e (A ⟨α, le_of_lt hα⟩)
            (A ⟨Order.succ α, Order.succ_le_of_lt hα⟩)),
          S.Countable ∧ Submodule.span R S = ⊤)) := by
  sorry

end DirectSum
