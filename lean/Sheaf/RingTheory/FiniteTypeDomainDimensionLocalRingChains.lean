module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries

/-! Common maximal-chain length part of the finite type domain dimension theorem.

Source: Stacks Project, Algebra, Lemma Tag 00OS, proof steps 1--6
(blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-chains)

Proof: present the domain as a quotient of a polynomial ring over the field.
Prime correspondence transfers maximal saturated chains to chains between the
kernel prime and maximal ideals. The polynomial height-difference theorem gives
their common length, and the same bound identifies it with the Krull dimension.
-/

@[expose] public section

universe u v

/-- The Krull dimension of a finite type domain over a field is a natural
number, and every maximal prime chain has that common length.  The proof uses
the polynomial presentation and the height-difference theorem for maximal
chains (Steps 1--6 of Tag 00OS).

Proof: present the algebra as a quotient of a multivariate polynomial ring,
transfer maximal prime chains along prime ideal correspondence, and apply the
polynomial height-difference theorem. The resulting common finite length is
the Krull dimension. (blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring-chains) -/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∃ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) ∧
      ∀ (p : LTSeries (PrimeSpectrum S)),
        IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p) →
          p.length = d := by
  sorry
