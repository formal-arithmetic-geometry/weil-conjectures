module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Auxiliary finite-component form of the prime-chain dimension argument.

Source: Stacks Project, Algebra, proof of Tag 00P1, lines 28238-28267.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum-data).

Proof: the minimal primes below `p` are finite and nonempty by Noetherianity.
Prime correspondence in the localization identifies chains below `p` with chains
in the local ring.  The maximal chain length is `d`; concatenating a maximal
chain above `p` of length `r` gives quotient dimension `d+r` for a component
attaining the maximum, and bounds every other component by the same number.
-/
theorem minimal_component_dimension_maximum_data
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∃ qs : Finset (Ideal S),
      (∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
        (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q)) ∧
      qs.Nonempty ∧
      ((∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞)) ∧
        (∃ q ∈ qs, ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry
