module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section
universe u v
namespace Ideal

/-- Height-one part of the fractional principal quotient associated-prime argument.
Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3).
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height)
The proof writes a nonzero fraction as `a / b`, embeds the quotient by `A ∩ yA`
into the principal quotient by `a`, and applies the normal-domain principal quotient
height theorem. -/
theorem associatedPrimes_fractionalPrincipalQuotient_height
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (y : K) (hy : y ≠ 0) :
    ∀ p ∈ associatedPrimes A
        (A ⧸ (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)),
      p.height = 1 := by
  sorry
end Ideal
