/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative

/-! # Representative normalization for tensor-Hom descent

The canonical theorem `AlgebraicGeometry.exists_tensorHomUncurry_descent_representative`
is proved in the adopted source library. Its K-flat hypothesis uses
`CochainComplex.IsKFlatTensor`, the acyclic-total-tensor definition of K-flatness.
This re-export restores the original module and exposes that theorem without a duplicate
declaration.

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-representative).
-/

@[expose] public section

