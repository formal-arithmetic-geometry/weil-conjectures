/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

-- Keep command elaboration available to the build's importing axiom/sorry probe.
-- This infrastructure import does not re-export the retired mathematical interface.
public import Mathlib.Init

/-!
# Retired duplicate equivariant sheaf module

The single retained theorem is
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`,
in `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`.
Callers import that module directly. This retired module has no declarations or
mathematical imports; its only import is
Mathlib.Init for the build probe. The equivariant sheaf statement and its proof remain
in the canonical module.
(blueprint: lem-weil-pbc-torsor-equivariant-presheaf-sheaf)
-/

@[expose] public section
