/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Complete intersections over a field

We define global and local complete intersections over a field, following Stacks.

## Main definitions

* `Algebra.IsGlobalCompleteIntersection`: a polynomial presentation of the expected dimension,
  including the zero ring by convention.
* `Algebra.IsLocalCompleteIntersection`: a cover by principal opens whose localizations are
  global complete intersections.

## References

* [Stacks, Tag 00S9] (Algebra, Definition 10.135.1)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A commutative `k`-algebra is a global complete intersection if it is the zero ring, or is
isomorphic as a `k`-algebra to a quotient of `k[x₁, ..., xₙ]` by `c ≤ n` polynomials and has Krull
dimension `n - c`. -/
def IsGlobalCompleteIntersection (k : Type u) (T : Type v) [Field k] [CommRing T]
    [Algebra k T] : Prop :=
  Subsingleton T ∨
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
      c ≤ n ∧
        Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T) ∧
        topologicalKrullDim (PrimeSpectrum T) = (↑(n - c) : WithBot ℕ∞)

/-- A finite type `k`-algebra is a local complete intersection if its spectrum is covered by
principal opens `D(g)` and every corresponding localization is a global complete intersection
over `k`. -/
def IsLocalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] : Prop :=
  ∃ s : Set S,
    (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ ∧
      ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

end Algebra
