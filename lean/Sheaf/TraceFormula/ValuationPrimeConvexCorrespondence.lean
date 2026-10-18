/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Sheaf.GroupTheory.OrderedGroupPrimeIdealConvex
import Sheaf.RingTheory.ValuationRingIdealCorrespondence

/-!
# Prime ideals and convex subgroups of a valuation ring

Source: Temkin, *Stable modification of relative curves*, §2.1, p. 7, lines 401–416;
Stacks Project, Algebra, Tags 00IE and 00IH
(blueprint: lem-trf-valuation-prime-convex-correspondence).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ValuationSubring

/-- The prime ideals of `A` correspond canonically, with inclusion reversed, to convex
subgroups of `Kˣ / A.unitGroup`. The quotient order is specified on representatives, and
membership of a nonzero element of `A` in the subgroup means that it is outside the prime.
Every strict prime chain gives a decreasing strict convex-subgroup chain of the same length.

Source: Temkin, *Stable modification of relative curves*, §2.1, p. 7, lines 401–416;
Stacks Project, Algebra, Tags 00IE and 00IH
(blueprint: lem-trf-valuation-prime-convex-correspondence).

Proof plan:
1. Multiplying representatives by units of `A` preserves membership in `A`, so the
   relation `[x] ≤ [y]` iff `y/x ∈ A` is well defined on the quotient. The valuation-ring
   alternative makes it total, and multiplication preserves it. Antisymmetry follows
   because `y/x` and its inverse both lie in `A` precisely when this quotient is a unit.
2. Apply `lem-trf-valuation-ring-ideal-correspondence` (Stacks Tag 00IH). It identifies
   ideals with upward-closed nonnegative value sets, preserving inclusion and primality.
3. Apply `lem-trf-ordered-group-prime-ideal-convex-correspondence`, written additively.
   A convex subgroup `H` corresponds to the nonnegative elements outside `H`; a prime
   cone ideal `I` corresponds to `{γ | |γ| ∉ I}`. Upward closure and primality make this
   a convex subgroup, and convexity makes the complement a prime cone ideal. These
   formulas are inverse and reverse inclusion.
4. Compose the two correspondences. For `x ∈ A` nonzero, its nonnegative value belongs
   to the resulting subgroup exactly when `x` is outside the prime ideal; this specifies
   the canonical map. The order isomorphism from the dual sends each increasing strict
   prime chain to a decreasing strict convex-subgroup chain, with the same `n` inclusions. -/
theorem primeSpectrum_orderDualEquiv_convexSubgroup {K : Type u} [Field K]
    (A : ValuationSubring K) :
    ∃ ord : LinearOrder (Kˣ ⧸ A.unitGroup),
      (∀ x y : Kˣ,
        ord.le (QuotientGroup.mk' A.unitGroup x) (QuotientGroup.mk' A.unitGroup y) ↔
          (y : K) / (x : K) ∈ A) ∧
      (∀ a b c : Kˣ ⧸ A.unitGroup, ord.le a b → ord.le (a * c) (b * c)) ∧
      ∃ e : (PrimeSpectrum A)ᵒᵈ ≃o
          {H : Subgroup (Kˣ ⧸ A.unitGroup) //
            ∀ ⦃h₁ h₂ g : Kˣ ⧸ A.unitGroup⦄, h₁ ∈ H → h₂ ∈ H →
              ord.le h₁ g → ord.le g h₂ → g ∈ H},
        (∀ (P : PrimeSpectrum A) (x : Kˣ) (hx : (x : K) ∈ A),
          QuotientGroup.mk' A.unitGroup x ∈ (e (OrderDual.toDual P)).1 ↔
            (⟨(x : K), hx⟩ : A) ∉ P.asIdeal) ∧
        (∀ (n : ℕ) (p : Fin (n + 1) → PrimeSpectrum A), StrictMono p →
          StrictAnti (fun i : Fin (n + 1) ↦ e (OrderDual.toDual (p i)))) := by
  sorry

end ValuationSubring
