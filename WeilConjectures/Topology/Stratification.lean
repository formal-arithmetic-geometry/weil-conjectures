/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.LocallyClosed

/-!
# Stratifications of topological spaces

Following [Stacks 09XZ], a *stratification* of a topological space `X` is a partition of
`X` into pairwise disjoint locally closed subsets covering `X`. `Topology.Stratification`
additionally requires the partition to be finite, the case relevant for constructible
sheaves.
-/

@[expose] public section

namespace Topology

/-- A *stratification* of a topological space `X`, following [Stacks 09XZ]: a finite
partition of `X` into pairwise disjoint locally closed subsets — the *strata* — covering
`X`. Finiteness is not required in loc. cit.; it is included here since finite
stratifications are the ones relevant for constructible sheaves. -/
@[stacks 09XZ]
structure Stratification (X : Type*) [TopologicalSpace X] where
  /-- The number of strata. -/
  n : ℕ
  /-- The strata. -/
  stratum : Fin n → Set X
  isLocallyClosed_stratum : ∀ i, IsLocallyClosed (stratum i)
  iUnion_stratum_eq_univ : ⋃ i, stratum i = Set.univ
  pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum)

end Topology
