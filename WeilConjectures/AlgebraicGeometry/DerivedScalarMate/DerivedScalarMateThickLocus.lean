/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateProjectionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateExactStructures
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-! # The derived scalar mate and its thick isomorphism locus

The normalized comparison data are publicly reexported from DerivedScalarMateData.
The geometric normalization and exact-structure lemmas are separate proof dependencies.
(blueprint: lem-sfb-derived-scalar-mate-thick-locus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

end AlgebraicGeometry.Scheme.DerivedScalarMate
