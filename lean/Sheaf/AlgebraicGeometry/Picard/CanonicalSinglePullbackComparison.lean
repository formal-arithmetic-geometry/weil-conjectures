/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

/-! # The pinned derived pullback comparison on a single module

Compatibility import for the adopted source implementation. It provides
`AlgebraicGeometry.Scheme.Modules.canonicalTensorPullbackAdditive`,
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackMap`, and
`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSinglePullbackMap`.

The comparison remains the specified derived counit followed by the single-complex
comparison and the unique tensor-to-ordinary pullback comparison.

Source: Stacks Project, Tags 06YD, 06YJ and 08HY.
(blueprint: lem-pc-canonical-single-pullback-comparison).
-/

@[expose] public section
