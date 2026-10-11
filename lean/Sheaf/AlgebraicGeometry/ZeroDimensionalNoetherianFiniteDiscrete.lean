/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension

/-!
# A Noetherian scheme of dimension at most zero is finite and discrete

Source: Stacks Project, Properties, Lemma 28.10.5 (Tag 0AAX), proof and conclusion
(blueprint: lem-sc-zero-dim-noetherian-finite-discrete).
-/

universe u

namespace AlgebraicGeometry

/-- A Noetherian scheme of topological Krull dimension at most zero has a finite discrete
underlying space: every point is closed and every singleton is open (`isClosed_discrete`,
`isOpen_discrete`). This includes the empty scheme.

Source: Stacks Project, Properties, Lemma 28.10.5 (Tag 0AAX), proof and conclusion
(blueprint: lem-sc-zero-dim-noetherian-finite-discrete).

Proof:
1. The underlying space is Noetherian by
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`. Local Noetherianity gives
   quasi-separatedness by `lem-weil-pbc-locally-noetherian-quasi-separated`, so
   `lem-weil-pbc-qcqs-scheme-spectral` gives spectrality (`def-weil-spectral-space`).
   It is therefore sober and T0: two distinct points with the same closure would be
   two generic points of the same irreducible closed subset, contradicting sobriety.
2. Apply `lem-sc-zero-dim-noetherian-closed-finite` to the whole closed space. The
   dimension bound gives finiteness and closedness of every singleton.
3. The complement of a singleton is a finite union of closed singletons, hence closed.
   Thus every singleton is open, so the space is discrete. For the empty scheme both
   singleton assertions are vacuous and its underlying type is finite.
-/
theorem finite_and_discreteTopology_of_topologicalKrullDim_le_zero
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) :
    Finite Y ∧ DiscreteTopology Y := by
  sorry

end AlgebraicGeometry
