/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.Algebra.Homology.KFlat
-- Preserve helper access for consumers using `import all` on this compatibility path.
import all WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Canonical tensor comparison for derived pullback

Compatibility import of the adopted source implementation, including the total tensor,
localization tensor map, canonical comparison predicate, model transport, existence and
uniqueness theorems. This keeps the original Sheaf import path usable without redeclaring
those constants. The source predicate uses `IsKFlatTensor`, whose definition agrees with
`IsAcyclicTensorKFlat` in the archived Sheaf implementation.

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison;
def-pc-derived-pullback-tensor-comparison-model-transport).
-/

@[expose] public section
