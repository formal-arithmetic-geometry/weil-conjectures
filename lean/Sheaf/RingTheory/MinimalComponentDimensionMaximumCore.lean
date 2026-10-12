module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The dimension bound for every minimal component below a prime.
Source: Stacks Project, Algebra, proof of Tag 00P1, lines 28238-28267.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum-bound).
Proof: put A = S/q and let P be the image of p in A. Ideal correspondence
identifies primes of A with primes of S containing q. The residue field of P
is canonically the residue field of p; it is the fraction field of A/P = S/p.
Thus the finite type domain dimension/transcendence-degree theorem gives
`dim(S/p) = r`. The maximal-chain theorem for that domain supplies a saturated
chain from p to a maximal ideal of S of length r.
Since hd bounds every chain below p by d, choose a longest chain from q to p,
of length s <= d. Such a chain exists: q <= p, and the set of possible natural
lengths is nonempty and bounded by d. It is saturated, and its first member is q.
Append the chosen chain above p, counting p only once. In the domain A, the
resulting chain starts at zero, ends at a maximal ideal, and is saturated, hence
is a maximal chain. The finite type domain maximal-chain theorem says its length
s+r is dim(A). Therefore dim(S/q) = s+r <= d+r.
-/
theorem minimal_component_dimension_maximum_bound
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∀ q : Ideal S, q.IsPrime → q ≤ p →
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) →
      ringKrullDim (S ⧸ q) ≤ ((d + r : ℕ) : WithBot ℕ∞) := by
  sorry

/-- Some minimal component below a prime attains the dimension bound.
Source: Stacks Project, Algebra, proof of Tag 00P1, lines 28238-28267.
(blueprint: lem-weil-pbc-minimal-component-dimension-maximum-attained).
Proof: localization prime correspondence identifies the lengths of chains
below p with those in S_p. Since hd is the finite natural number d, the supremum
of these lengths is attained: if no chain had length d, all lengths would be
at most d-1 (and for d=0 the single-prime chain already attains it).
A length-d chain below p ends at p and starts at a minimal prime q of S;
otherwise appending p or prepending a smaller prime would contradict the bound d.
It is saturated for the same reason. Ideal correspondence gives a saturated
chain from zero to the image of p in the finite type domain S/q.
The residue field of p is the fraction field of S/p. The finite type domain
dimension/transcendence-degree theorem and hr give dim(S/p) = r, and the
maximal-chain theorem supplies a saturated chain of length r above p ending
at a maximal ideal. Append this to the length-d chain, counting p only once.
It is a maximal chain in S/q. The domain maximal-chain theorem makes its length
d+r equal to dim(S/q), giving the required q, its primality and minimality.
-/
theorem minimal_component_dimension_maximum_attained
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (d r : ℕ)
    (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞))
    (hr : Algebra.trdeg k p.ResidueField = (r : Cardinal.{v})) :
    ∃ q : Ideal S, q.IsPrime ∧ q ≤ p ∧
      (∀ t : Ideal S, t.IsPrime → t ≤ q → t = q) ∧
      ringKrullDim (S ⧸ q) = ((d + r : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
