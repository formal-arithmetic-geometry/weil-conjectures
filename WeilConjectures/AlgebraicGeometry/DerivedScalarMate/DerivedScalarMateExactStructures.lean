/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ProEtaleProjectionFirstVariableExact
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateProjectionNormalization
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import all WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact

/-! # Canonical exact structures of the scalar mate

Source: Stacks Project, Tags 03EL, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-derived-scalar-canonical-exact-structures).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  AlgebraicGeometry.Scheme.ProjectionRestriction.resolving
  AlgebraicGeometry.Scheme.proEtaleFlatRepresentatives
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

open ProjectionRestriction

end AlgebraicGeometry.Scheme.DerivedScalarMate
