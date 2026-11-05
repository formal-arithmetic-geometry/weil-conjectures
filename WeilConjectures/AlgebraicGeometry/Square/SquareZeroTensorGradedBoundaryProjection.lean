/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.CategoryTheory.Abelian.ResolvedBoundaryNaturality

/-! # Naturality of homogeneous boundary projections

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-boundary-projection).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
attribute [local irreducible] RingedSpace.moduleSectionBoundary Functor.rightDerived tensorPullback
  Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  InjectiveResolution.isoRightDerivedObj DerivedCategory.HomologySequence.δ
  ShortComplex.ShortExact.δ tensorGradedAlgebraMap Functor.mapHomologicalComplex
  Functor.rightDerivedFunctorPlus ShortComplex.ShortExact.singleTrianglePlus
attribute [local instance] boundary_enoughInjectives
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
