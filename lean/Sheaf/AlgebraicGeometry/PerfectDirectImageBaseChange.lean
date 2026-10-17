/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F1 and H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange

/-! # Retired perfect direct image compatibility module

The blueprint node `lem-pc-rf-perfect-base-change` is recorded at
`AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`.
This module re-exports its source module. Former derived-category users now use
`properFlat_single_derivedDirectImage_perfect` for perfectness and the canonical
relatively flat module base-change API for the particular comparison they need.
The source theorem's Cech statement is not identified with the stronger retired statement.
-/

@[expose] public section
