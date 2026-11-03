/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Constructions

/-! # Profinite integers as compatible residue families

Source: Stacks Project, Tag 0BR1, `topology-lemma-profinite-group`, finite-quotient
presentation, specialized to integer residues as in the auxiliary power-map construction
(blueprint: def-sf-profinite-integers).

All positive moduli occur, with `ZMod.castHom` as reduction. The additive subgroup inherits
coordinatewise operations and the subtype topology of the product of discrete residue rings.
-/

@[expose] public section

set_option autoImplicit false

/-- The positive modulus index for the explicit profinite-integer limit.
Source: Stacks Project, Tag 0BR1, topology-lemma-profinite-group
(blueprint: def-sf-profinite-integers). -/
abbrev profiniteIntegerIndex := {n : ℕ // 0 < n}

/-- The additive group of compatible residues modulo every positive integer.
Source: Stacks Project, Tag 0BR1, topology-lemma-profinite-group
(blueprint: def-sf-profinite-integers). -/
def profiniteIntegerLimit : AddSubgroup (∀ n : profiniteIntegerIndex, ZMod n.1) where
  carrier := {a | ∀ (m n : profiniteIntegerIndex) (h : m.1 ∣ n.1),
    ZMod.castHom h (ZMod m.1) (a n) = a m}
  zero_mem' := by
    intro m n h
    simp
  add_mem' := by
    intro a b ha hb m n h
    simp only [Pi.add_apply, map_add]
    rw [ha m n h, hb m n h]
  neg_mem' := by
    intro a ha m n h
    simp only [Pi.neg_apply, map_neg]
    rw [ha m n h]

/-- The diagonal embedding of the integers into the profinite-integer limit.
Source: Stacks Project, Tag 0BR1, topology-lemma-profinite-group
(blueprint: def-sf-profinite-integers). -/
def profiniteIntegerInt (m : ℤ) : profiniteIntegerLimit :=
  ⟨fun n ↦ (m : ZMod n.1), by
    intro a b h
    simp⟩

end
