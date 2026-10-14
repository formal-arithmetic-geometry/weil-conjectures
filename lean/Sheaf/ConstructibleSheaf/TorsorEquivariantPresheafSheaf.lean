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
`TorsorEquivariantModuleIsSheaf`. This public import re-exports
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`
for callers using the historical module path. The declaration is defined exactly once,
so this compatibility module intentionally contains no additional declarations.
The canonical implementation remains centralized in the imported module.
This file is retained as the compatibility entry point after duplicate removal.
Callers should import this module when they need the canonical theorem under
the historical compatibility path.
(blueprint: lem-weil-pbc-torsor-equivariant-presheaf-sheaf)
-/

@[expose] public section

-- The duplicate-removal repair is complete: the imported module contains the sole proof.
-- Keep this public import so historical callers receive that same declaration.
