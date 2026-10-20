/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence

/-! # Independence of localized tensor-Hom evaluation from chain representatives

The canonical theorem `AlgebraicGeometry.tensorHomUncurry_representative_coherence`
is provided by the adopted source library. Its K-flat hypotheses use
`CochainComplex.IsKFlatTensor`, the acyclic-total-tensor definition of K-flatness.
This re-export keeps the original module available without declaring the same theorem twice.

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-representative-coherence).
-/

@[expose] public section
