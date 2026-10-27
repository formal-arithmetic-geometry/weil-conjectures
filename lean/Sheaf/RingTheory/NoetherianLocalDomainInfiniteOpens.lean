module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Infinite nonempty opens in a high-dimensional Noetherian local domain

Source: Stacks Project, Algebra, Tag 02IG,
`lemma-Noetherian-local-domain-dim-2-infinite-opens`
(blueprint: lem-per-noetherian-local-domain-open-infinite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Every nonempty open in the spectrum of a Noetherian local domain of dimension at least
 two is infinite. Source: Stacks Project, Algebra, Tag 02IG,
`lemma-Noetherian-local-domain-dim-2-infinite-opens`
(blueprint: lem-per-noetherian-local-domain-open-infinite).

Proof plan:
1. Suppose the open O is finite. The generic point (0) belongs to O because its closure is
   the whole spectrum. Remove the finitely many closures of the other points of O. None
   contains (0), so the remaining singleton {(0)} is open. This uses the closure description
   of lem-weil-pbc-spec-irreducible-closed-subsets-primes.
2. By def-weil-pbc-krull-dimension-ring and
   lem-weil-pbc-noetherian-local-system-of-parameters, the dimension is a finite integer d
   with d at least two. In particular the spectrum is not a singleton.
3. The basis clause of lem-weil-pbc-spec-localization-away-basic-open gives an element x
   with D(x) = {(0)}. It is nonzero and not a unit, hence belongs to the maximal ideal.
4. The quotient R/(x) is a nonzero Noetherian local ring. The element x is a nonzerodivisor,
   since R is a domain. By lem-weil-pbc-dimension-quotient-nonzerodivisor its dimension is
   d - 1, which is at least one.
5. Apply lem-weil-pbc-noetherian-local-system-of-parameters to this quotient, obtaining
   parameters y_2,...,y_d whose generated ideal contains a power of its maximal ideal.
   Lift them into the maximal ideal of R. The radical of (x,y_2,...,y_d) is the maximal
   ideal: the power containment proves one inclusion, and primality proves the other.
6. Reorder the parameters as y_2,x,y_3,...,y_d. Apply
   lem-per-partial-parameters-quotient-dimension with i = 1 and i = 2 to obtain dimensions
   d - 1 for R/(y_2) and d - 2 for R/(y_2,x).
7. The first equality forces y_2 to be nonzero. If every prime containing y_2 also contained
   x, the quotient-prime correspondence would identify all prime chains in the two
   quotients, contradicting their different dimensions. Thus there is a prime containing
   y_2 but not x. It belongs to D(x) = {(0)} yet is nonzero, the final contradiction. -/
theorem Spec.infinite_of_isOpen_of_two_le_topologicalKrullDim
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hdim : 2 ≤ topologicalKrullDim (Spec (CommRingCat.of R)))
    (O : Set (Spec (CommRingCat.of R))) (hO : IsOpen O) (hne : O.Nonempty) :
    O.Infinite := by
  sorry

end AlgebraicGeometry
