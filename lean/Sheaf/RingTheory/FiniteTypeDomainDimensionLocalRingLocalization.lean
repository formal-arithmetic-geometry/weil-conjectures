module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-! Localization dimension part of the finite type domain dimension theorem.

Source: Stacks Project, Algebra, Lemma Tag 00OS, proof steps 1--5
(blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-localization)

Proof: present the finite type domain as a quotient of a polynomial ring.
Prime correspondence identifies primes below a maximal ideal with primes in
the polynomial ring above the kernel. Polynomial localization dimension and
height-difference results show both dimensions equal the same finite height
difference.
-/

@[expose] public section

universe u v

/-- Every maximal localization of a finite type domain over a field has the
same Krull dimension as the domain.  The proof uses a polynomial presentation,
prime ideal correspondence, and the maximal-chain height theorem for
polynomial rings; these are exactly Steps 1--5 of Tag 00OS.

Proof: present the algebra as a quotient of a multivariate polynomial ring,
identify primes below a maximal ideal with primes above the kernel, and use
the polynomial localization-dimension and height-difference theorems to show
that both dimensions equal the same finite height difference.
(blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-localization) -/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∀ (m : Ideal S) [m.IsMaximal],
      ringKrullDim (Localization.AtPrime m) = ringKrullDim S := by
  sorry

