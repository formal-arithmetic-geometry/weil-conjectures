/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison

/-! # Open restriction comparison for derived projection mates

Compatibility import for the canonical upstream theorem
`AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison`.
This module intentionally adds no second declaration: the upstream module is the
canonical proof and this path preserves the Sheaf namespace import contract.
The upstream proof constructs the quasi-coherent restrictions, descends the adjunction
and tensor comparison, and proves the mate square by naturality of the Hom equivalence.

Source: Stacks Project, Tag 08EU (first sentence of the proof) and Tag 08FE.
(blueprint: lem-pc-derived-projection-mate-open-restriction-comparison).
-/

@[expose] public section
