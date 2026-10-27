module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-! # Elementary finite groups for Brauer induction

Source: the elementary-group definition in the accepted auxiliary character-unit node;
ILO, Exposé X, Proposition 1.2, p.138 supplies representation-theoretic context only.
Serre, Linear Representations of Finite Groups, Part II, Chapter 10, §§10.2–10.3 is wanted.
(blueprint: def-per-brauer-elementary-group)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Group

/-- A finite group is elementary if it is a product of a cyclic prime-to-p group and a
p-power-order group for some prime p. The factors are subgroups of G: the images of the two
abstract factors under any product isomorphism give exactly these witnesses, so no universe
restriction on abstract presentations is imposed. The isomorphism need not be multiplication
of the chosen subgroups; only their abstract product type matters.
Source: the definition in lem-per-brauer-elementary-unit-character, with ILO X 1.2, p.138
as motivation and Serre II, Chapter 10, §§10.2–10.3 as the wanted reference.
(blueprint: def-per-brauer-elementary-group) -/
def IsBrauerElementary (G : Type u) [Group G] [Finite G] : Prop :=
  ∃ (p a : ℕ) (C P : Subgroup G),
    p.Prime ∧ IsCyclic C ∧ (Nat.card C).Coprime p ∧ Nat.card P = p ^ a ∧
      Nonempty ((C × P) ≃* G)

end Group
