/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # The induced triangulation on algebraic-space D_QCoh

Source: Stacks Project, Derived Categories of Spaces, definition-derived-quasi-coherent;
Derived Categories, Tag 06UP
(blueprint: def-sfb-space-qcoh-derived-triangulation).
The category is the existing full subcategory, with the ambient shifts and triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The existing quasi-coherent derived subcategory inherits its triangulation.
Source: Stacks Project, definition-derived-quasi-coherent; Derived Categories, Tag 06UP
(blueprint: def-sfb-space-qcoh-derived-triangulation).

Proof: zero has quasi-coherent cohomology. Shifts reindex the same cohomology sheaves.
In a distinguished triangle the long exact cohomology sequence expresses the middle
cohomology as an extension of a cokernel by a kernel. Quasi-coherent modules on an
algebraic space are closed under kernels, cokernels and extensions, as checked on
affine etale charts. Transport through the recorded module equivalence preserves
these constructions. This gives ContainsZero, shift stability and triangle closure,
the fields of ObjectProperty.IsTriangulated. -/
@[instance] theorem derivedQCohProperty_isTriangulated
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    X.derivedQCohProperty.IsTriangulated := by
  sorry

/-- The inherited pretriangulation, using Mathlib's full-subcategory construction.
Source: Stacks Project, definition-derived-quasi-coherent; Derived Categories, Tag 06UP
(blueprint: def-sfb-space-qcoh-derived-triangulation). -/
abbrev qcohDerivedTriangulation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : Pretriangulated X.DerivedQCoh :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace
