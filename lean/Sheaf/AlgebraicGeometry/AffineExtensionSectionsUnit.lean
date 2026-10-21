/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnit

/-! # The affine extension-of-sections unit

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.exists_affineExtensionSectionsUnit`; the source
dropped the redundant identity hypothesis `hv`.
The source module `WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnit` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-extension-sections-unit).
-/

@[expose] public section
