/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel

/-! # Underived model of affine extension of sections

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.exists_affineExtensionSections_underived_model`; the source
dropped the redundant identity hypothesis `hv`.
The source module `WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-extension-sections-underived-model).
-/

@[expose] public section
