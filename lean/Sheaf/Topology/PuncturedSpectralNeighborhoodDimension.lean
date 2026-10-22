/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.KrullDimension
public import Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram
import WeilConjectures.Topology.SpectralGeneralizations
import Sheaf.Topology.SpectralDirectedLimit

/-! # Spectrality and dimension of punctured generalization neighborhoods

Source: Stacks Project, Topology, Tag 0AP0; Cohomology, Tag 0A3G, induction step (2).
(blueprint: lem-sfb-punctured-spectral-neighborhood-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Topology

/-- The generalizations of a closed subset with quasi-compact open complement, after
removing that subset, form a spectral space of dimension at most one less than the
ambient dimension bound.

Source: Stacks Project, Topology, Tag 0AP0 (`lemma-make-spectral-space-minus`), and
Cohomology, Tag 0A3G (`proposition-cohomological-dimension-spectral`), induction step (2).
(blueprint: lem-sfb-punctured-spectral-neighborhood-dimension)

Proof:
1. Put U = X \ Z and W = {x | closure {x} meets Z}. Closedness makes Z compact.
By `lem-weil-pbc-spectral-generalizations-of-quasi-compact`, W is the intersection
of all compact open neighborhoods N of Z. These neighborhoods contain X as a member
and are directed under reverse inclusion, since intersections of compact opens are compact.
Thus S = W \ Z is the intersection of the compact opens N ∩ U.
2. Each N ∩ U is spectral: the ambient compact-open basis and finite-intersection
property restrict to this compact open subspace. For sobriety, take the ambient closure
of an irreducible closed subset of N ∩ U. Its ambient generic point lies in the open
N ∩ U, and is the unique generic point of the original subset. The transition inclusions
are spectral, because inverse images of compact opens are intersections of compact opens.
3. The inclusions exhibit S as the inverse limit of these subspaces: compatibility
identifies all coordinates with one ambient point, using the coordinate at intersections.
Such a point is precisely in S. The coordinate N = X induces the subspace topology.
Apply `lem-weil-pbc-spectral-directed-limit-spectral` to obtain spectrality of S.
4. For a strict chain C₀ ⊊ ⋯ ⊊ Cₘ of irreducible closed subsets of S, choose their
generic points ηᵢ. Their ambient closures Dᵢ form a strict chain in X: intersecting
with S recovers Cᵢ, and ηᵢ ∈ Dᵢ₊₁ gives inclusion of the ambient closures.
5. Since η₀ is in W, choose z in Z ∩ closure {η₀}. The irreducible closed set
closure {z} lies in D₀ ∩ Z, strictly inside D₀ because η₀ is not in Z. Prepending
it gives a chain of length m + 1 in X. Thus m + 1 ≤ n and m ≤ n - 1.
Taking the supremum of all chain lengths proves the dimension bound.
6. If Z is empty, Z = X, or X is empty, S is empty. The directed index still
contains X, spectrality holds for the empty space, and its dimension is bottom (-∞).
No nonemptiness assumption was used except when testing an actual chain. -/
theorem spectralSpace_puncturedGeneralizations_and_dimension
    (X : Type u) [TopologicalSpace X] [SpectralSpace X]
    (n : ℕ) (hn : 1 ≤ n) (hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (Z : Set X) (hZ : IsClosed Z) (hU : IsCompact Zᶜ) :
    SpectralSpace (TopCat.puncturedGeneralizations Z) ∧
      topologicalKrullDim (TopCat.puncturedGeneralizations Z) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

end Topology
