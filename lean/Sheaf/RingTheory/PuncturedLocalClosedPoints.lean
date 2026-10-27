module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyClosed
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.KrullDimension

/-! # Closed points in the punctured spectrum of a Noetherian local ring

Source: Stacks Project, Properties Tag 02IM (1), Morphisms Tag 02J6 (4), and the
locally closed characterization following Topology Tag 005U.
(blueprint: lem-per-punctured-local-closed-points)
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Every nonempty locally closed subset of the punctured local spectrum contains a point
closed in that punctured spectrum. The subtype carries the subspace topology.

Source: Stacks Project, Properties Tag 02IM (1), equivalently Morphisms Tag 02J6 (4),
using the characterization following Topology Tag 005U.
(blueprint: lem-per-punctured-local-closed-points)

Proof plan:
1. The closed sets of Spec A are the zero loci of ideals. The radical formula and finite
   generation of ideals show that descending chains of closed sets stabilize
   (`lem-weil-pbc-spec-irreducible-closed-subsets-primes`,
   `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, `def-weil-pbc-noetherian-ring`).
   The singleton-closure formula also gives the T0 property, inherited by W.
2. Every subset of this Noetherian space is quasi-compact
   (`lem-sfb-noetherian-space-compact-subsets`). Apply
   `lem-sc-quasi-compact-kolmogorov-closed-point` to W to choose w closed in W.
3. Every prime lies in the unique maximal ideal
   (`lem-weil-pbc-proper-ideal-contained-in-maximal`), so the puncture U is open.
   Write W = O ∩ F in U and {w} = W ∩ C with C closed in U. Then
   {w} = O ∩ closure {w} in U. The singleton-closure formula shows that, if p is
   the prime of w, {p} is open in V(p), including its ambient closed point.
4. If w is not closed in U, there is p < q < m. The quotient B = A/p is a nonzero
   local domain (`lem-weil-pbc-quotient-local-structure`) and is Noetherian: the
   images of finite generators of the inverse image generate each quotient ideal.
5. The homeomorphism Spec B ≃ V(p)
   (`lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`) transfers the open singleton
   to the zero prime of B. The chain 0 < q/p < m/p gives dimension at least two
   (`def-kun-topological-krull-dimension` and the singleton-closure formula).
6. The nonempty finite open singleton contradicts
   `lem-per-noetherian-local-domain-open-infinite`. Thus w is closed in U. -/
theorem exists_isClosed_singleton_of_isLocallyClosed_punctured
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (W : Set {x : AlgebraicGeometry.Spec (CommRingCat.of A) |
      x ≠ IsLocalRing.closedPoint A})
    (hW : W.Nonempty) (hWlc : IsLocallyClosed W) :
    ∃ w ∈ W, IsClosed ({w} : Set {x : AlgebraicGeometry.Spec (CommRingCat.of A) |
      x ≠ IsLocalRing.closedPoint A}) := by
  sorry

end PrimeSpectrum
