/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Algebra.Homology.LocalCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Dimension bounds for isolated intersections

Source: Stacks Project, Local Cohomology, Lemma 0DXF, including its closed-subset
consequence (blueprint: lem-per-isolated-intersection-dimension-bound).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- If a closed subset of the spectrum of a nonzero finite-dimensional Noetherian local
ring meets `V(I)` only at the closed point, its dimension is at most `cd(A,I)`. In particular,
the same bound holds for the dimension of `A/p` when `V(p)` has this intersection property.
The spectrum below is the underlying space of `AlgebraicGeometry.Spec (.of A)`.
Source: Stacks Project, Local Cohomology, Lemma 0DXF
(blueprint: lem-per-isolated-intersection-dimension-bound).

Proof: write `Z = V(J)`. The intersection hypothesis puts the maximal ideal in `Z`, so
`B = A/J` is a nonzero Noetherian local ring. The quotient-spectrum homeomorphism
[lem-weil-pbc-spec-quotient-homeomorphism-zero-locus] identifies `Spec B` with `Z` and hence
identifies their dimensions; the dimension is finite because `Z` is a closed subspace.
The same homeomorphism gives `V(IB) = {m/J}`. The radical description
[lem-weil-pbc-zero-locus-eq-iff-radical-eq] therefore gives `radical (IB) = m/J`.
Choose generators of `m/J` and powers of each generator belonging to `IB`. The monomial
pigeonhole argument gives `(m/J)^N ≤ IB ≤ m/J` for some positive `N`; for no generators take
`N = 1`. Thus their ideal-power torsion subfunctors, and their right derived functors, agree.
Apply [lem-per-local-cohomology-change-rings] to `A → B`, and apply
[lem-per-local-cohomology-top-nonvanishing] in degree `dim B`. The latter forces
`dim Z = dim B ≤ cd(B,m/J) = cd(B,IB) ≤ cd(A,I)`. Finally take `Z = V(p)` and use the
quotient-spectrum homeomorphism again to obtain the prime-quotient clause. -/
theorem isolated_intersection_dimension_bound
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hfinite : topologicalKrullDim (PrimeSpectrum A) < ⊤)
    (I : Ideal A) (hI : I ≠ ⊤) :
    (∀ Z : Set (PrimeSpectrum A), IsClosed Z →
      Z ∩ zeroLocus (I : Set A) = {IsLocalRing.closedPoint A} →
      topologicalKrullDim Z ≤ ModuleCat.localCohomologicalDimension I) ∧
    (∀ p : PrimeSpectrum A,
      zeroLocus (p.asIdeal : Set A) ∩ zeroLocus (I : Set A) =
        {IsLocalRing.closedPoint A} →
      topologicalKrullDim (PrimeSpectrum (A ⧸ p.asIdeal)) ≤
        ModuleCat.localCohomologicalDimension I) := by
  sorry

end PrimeSpectrum
