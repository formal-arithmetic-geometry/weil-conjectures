/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximumData

/-!
# Dimensions of the minimal components through a prime

For a prime `p` of a finite type algebra `S` over a field, the maximum of `dim S/q` over the
minimal primes `q ⊆ p` equals `dim S_p + trdeg κ(p)`.

## Implementation details

Every maximal chain of primes in `S/p` has length `r = trdeg κ(p)` (Stacks 00P0, 00OS). For each
minimal `q ⊆ p`, a saturated chain from `q` to `p` of greatest length `s(q) ≤ d` is concatenated
with a fixed maximal chain above `p`, giving a maximal chain in `S/q`, so `dim S/q = s(q) + r`;
some `q` attains `s(q) = d`. No topological dimension-at-point formula is used.

## References

* [Stacks, Tag 00P1] (proof, the prime-chain argument)
* [Stacks, Tags 00P0, 00OS]
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The maximum dimension of the minimal components through a prime is the sum of the
local-ring dimension and the residue transcendence degree. This is a ring-theoretic
statement, before identifying that maximum with topological dimension at the point. -/
theorem minimal_component_dimension_maximum
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    (∀ q : Ideal S, q.IsPrime → q ≤ p →
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) →
      ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞)) ∧
    (∃ q : Ideal S, q.IsPrime ∧ q ≤ p ∧
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) ∧
      ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞)) := by
  obtain ⟨qs, hqs, hne, hbound, hattain⟩ :=
    minimal_component_dimension_maximum_data (k := k) p d r hd hr
  constructor
  · intro q hq hqp hmin
    have hqmem : q ∈ qs := (hqs q).mpr ⟨hq, hqp, hmin⟩
    exact hbound q hqmem
  · obtain ⟨q, hq, hqeq⟩ := hattain
    obtain ⟨hprime, hbelow, hminimal⟩ := (hqs q).mp hq
    exact ⟨q, hprime, hbelow, hminimal, hqeq⟩

end AlgebraicGeometry
