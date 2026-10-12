module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section
universe u v
namespace Ideal

/-- Minimal-prime part of the fractional principal quotient associated-prime argument.
Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3).
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal)
The proof identifies the annihilator of an associated class, observes that it contains
`A ∩ yA`, and excludes a strictly smaller prime using the nonzero numerator and the
height-one conclusion. -/
theorem associatedPrimes_fractionalPrincipalQuotient_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (y : K) (hy : y ≠ 0) :
    ∀ p ∈ associatedPrimes A
        (A ⧸ (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)),
      p ∈ Ideal.minimalPrimes
        ((Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)) := by
  sorry
end Ideal
