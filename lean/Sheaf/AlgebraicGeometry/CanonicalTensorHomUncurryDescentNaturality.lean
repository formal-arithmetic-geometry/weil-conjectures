/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality

/-! Compatibility re-export of the canonical upstream proof.

The upstream theorem uses `CochainComplex.IsKFlatTensor`, the current name for
the acyclic-tensor K-flatness predicate. No duplicate declarations are introduced.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).
-/

@[expose] public section
