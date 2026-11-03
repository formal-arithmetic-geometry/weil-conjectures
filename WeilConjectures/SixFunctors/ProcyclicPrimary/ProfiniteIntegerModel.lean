/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Pi.Basic

/-! # The residue model of the profinite integers

Source: blueprint latest, part-six-operations/sec-smooth-base-change/sec-sbc-uniform/
sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md, counterexample
paragraph; the residue construction in lem-sf-profinite-integer-powers.
(blueprint: def-sf-profinite-integer-model)
-/

@[expose] public section
set_option autoImplicit false

universe u

namespace ProcyclicPrimary

/-- Compatible residues at every positive modulus, with the inherited product topology.
Source: lem-sf-profinite-integer-powers, residue-limit construction.
(blueprint: def-sf-profinite-integer-model) -/
def integerResidues : AddSubgroup ((n : ℕ+) → ZMod n.1) where
  carrier := {a | ∀ (m n : ℕ+) (h : m.1 ∣ n.1),
    ZMod.castHom h (ZMod m.1) (a n) = a m}
  zero_mem' := by
    intro m n h
    exact (ZMod.castHom h (ZMod m.1)).map_zero
  add_mem' := by
    intro a b ha hb m n h
    change ZMod.castHom h (ZMod m.1) (a n + b n) = a m + b m
    rw [map_add, ha m n h, hb m n h]
  neg_mem' := by
    intro a ha m n h
    change ZMod.castHom h (ZMod m.1) (-a n) = -a m
    rw [map_neg, ha m n h]

/-- The `r`-supported residues: all coordinates at powers of other primes vanish.
Source: blueprint latest, scope counterexample, pro-r part of the procyclic subgroup.
(blueprint: def-sf-profinite-integer-model) -/
def supportedResidues (r : ℕ) : AddSubgroup integerResidues where
  carrier := {a | ∀ (l : ℕ) (hl : l.Prime), l ≠ r → ∀ k : ℕ,
    a.1 ⟨l ^ k, pow_pos hl.pos k⟩ = 0}
  zero_mem' := by
    intro l hl hne k
    rfl
  add_mem' := by
    intro a b ha hb l hl hne k
    change a.1 ⟨l ^ k, pow_pos hl.pos k⟩ + b.1 ⟨l ^ k, pow_pos hl.pos k⟩ = 0
    rw [ha l hl hne k, hb l hl hne k, add_zero]
  neg_mem' := by
    intro a ha l hl hne k
    change -a.1 ⟨l ^ k, pow_pos hl.pos k⟩ = 0
    rw [ha l hl hne k, neg_zero]

/-- Image of the supported residues under the power homomorphism.
Source: blueprint latest, scope counterexample, primary part construction.
(blueprint: def-sf-profinite-integer-model) -/
def primaryImage {C : Type u} [Group C]
    (q : Multiplicative integerResidues →* C) (r : ℕ) : Subgroup C :=
  (supportedResidues r).toSubgroup.map q

end ProcyclicPrimary
