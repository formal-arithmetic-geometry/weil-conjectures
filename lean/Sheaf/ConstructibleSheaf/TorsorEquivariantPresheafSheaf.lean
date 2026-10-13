/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf

/-!
# Compatibility import for equivariant locally constant sections

The scalar-restricted sheaf theorem has a single implementation in
`TorsorEquivariantModuleIsSheaf`. This public import makes
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` available
to callers without a second declaration or gluing proof.
This compatibility module intentionally contains no additional declarations.
(blueprint: lem-weil-pbc-torsor-equivariant-presheaf-sheaf)
-/

@[expose] public section
