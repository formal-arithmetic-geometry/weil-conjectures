/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Prime positive-cone ideals and convex subgroups

Source: literature/stacks-project/algebra.tex, Tag 00IE (blueprint:
lem-trf-ordered-group-prime-ideal-convex-correspondence).
-/

@[expose] public section

universe u

open Set

namespace AddSubgroup

/-- Prime ideals of the nonnegative cone of a totally ordered abelian group are canonically
order anti-isomorphic to its convex additive subgroups, with the specified carrier formulas.

Source: literature/stacks-project/algebra.tex, Tag 00IE, `definition-value-group`, for the
ordered-group conventions; the correspondence is proved by the following elementary argument
(blueprint: lem-trf-ordered-group-prime-ideal-convex-correspondence).

Proof: Translation reverses inequalities under negation. Totality gives `|x| = x` or `-x`,
so `0 ≤ |x|`, `|0| = 0`, `|-x| = |x|`, and `-|x| ≤ x ≤ |x|`. Adding these bounds gives
`|x + y| ≤ |x| + |y|`. For a convex subgroup `H`, its nonnegative complement excludes zero;
if `a` belongs to it and `a ≤ b`, then `b ∈ H` would imply `a ∈ H` by convexity between
zero and `b`. The complement is prime since two nonnegative elements of `H` have sum in `H`.
For a prime ideal `I`, its complement `S` in the nonnegative cone contains zero, is downward
closed by upward closure of `I`, and is addition-closed by primality. The absolute-value
identities and triangle inequality therefore make `{x | |x| ∉ I}` a subgroup. For convexity,
if `a ≤ x ≤ b` with `a,b` in this subgroup, split into `0 ≤ x` and `x ≤ 0`: respectively
`|x| ≤ |b|` and `|x| ≤ |a|`, so downward closure applies. Finally, `|x| ∈ H ↔ x ∈ H` by
negation closure, and `|a| = a` for nonnegative `a`; these give the two inverse identities.
Taking complements reverses both inclusions, giving the stated order isomorphism from the
order dual. The formulas determine both maps uniquely. -/
theorem orderedGroup_primePositiveConeIdeal_orderDualEquiv_convexAddSubgroup
    {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] :
    ∃ e :
        ({I : Set Γ //
            (∀ ⦃x : Γ⦄, x ∈ I → 0 ≤ x) ∧
            (∀ ⦃x y : Γ⦄, x ∈ I → x ≤ y → y ∈ I) ∧
            0 ∉ I ∧
            (∀ ⦃x y : Γ⦄, 0 ≤ x → 0 ≤ y → x + y ∈ I → x ∈ I ∨ y ∈ I)})ᵒᵈ ≃o
          {H : AddSubgroup Γ //
            ∀ ⦃h₁ h₂ x : Γ⦄, h₁ ∈ H → h₂ ∈ H → h₁ ≤ x → x ≤ h₂ → x ∈ H},
      (∀ (I : {I : Set Γ //
          (∀ ⦃x : Γ⦄, x ∈ I → 0 ≤ x) ∧
          (∀ ⦃x y : Γ⦄, x ∈ I → x ≤ y → y ∈ I) ∧
          0 ∉ I ∧
          (∀ ⦃x y : Γ⦄, 0 ≤ x → 0 ≤ y → x + y ∈ I → x ∈ I ∨ y ∈ I)}),
          ∀ γ : Γ,
            γ ∈ (e (OrderDual.toDual I)).1 ↔ |γ| ∉ I.1) ∧
        (∀ (H : {H : AddSubgroup Γ //
          ∀ ⦃h₁ h₂ x : Γ⦄, h₁ ∈ H → h₂ ∈ H → h₁ ≤ x → x ≤ h₂ → x ∈ H}),
          ∀ γ : Γ,
            γ ∈ (e.symm H).1 ↔ 0 ≤ γ ∧ γ ∉ H.1) := by
  sorry

end AddSubgroup
