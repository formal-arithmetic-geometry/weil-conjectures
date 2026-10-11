/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Ample

/-! # Affineness and ampleness in dimension zero

Source: Stacks Project, Properties, Lemmas 0AAX and 0CKV, and Definition 01PS
(blueprint: lem-sc-zero-dim-noetherian-affine).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A Noetherian separated scheme of topological Krull dimension at most zero is affine,
and its trivial invertible module is ample. The empty scheme is included.
Source: Stacks Project, Properties, Lemmas 0AAX and 0CKV, and Definition 01PS
(blueprint: lem-sc-zero-dim-noetherian-affine).

Proof:
1. The empty scheme is affine and its structure sheaf is ample (the pointwise condition
is vacuous). Otherwise, Noetherianity makes the underlying space Noetherian
(`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`). By the dimension bound and
Stacks 0AAX, its topology is finite and discrete
(`lem-sc-zero-dim-noetherian-finite-discrete`).
2. Quasi-compactness and separatedness, together with this finite discrete topology,
give affineness by `lem-sc-finite-discrete-separated-affine` (Stacks 0CKV).
3. Quasi-compactness is condition (1) of ampleness. For each point, take tensor power
`n = 1` and section `1` of the structure sheaf. Its nonvanishing locus is all of the
scheme, which is affine by step 2. This gives condition (2) of
`def-weil-pbc-ample-invertible-module`, using `def-sc-invertible-module` and
`def-weil-affine-spectrum`.
-/
theorem isAffine_and_isAmple_tensorUnit_of_dim_le_zero (Y : Scheme.{u})
    [IsLocallyNoetherian Y] [CompactSpace Y] [Y.IsSeparated]
    (hdim : topologicalKrullDim Y ≤ 0) :
    IsAffine Y ∧ IsAmple Y (𝟙_ Y.Modules) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
