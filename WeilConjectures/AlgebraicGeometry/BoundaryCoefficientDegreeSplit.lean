/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # Splitting off the first coefficient block

Source: Stacks Project, Tags 01CD and 09MS.
(blueprint: lem-sc-boundary-coefficient-degree-split).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

-- The next two helpers adapt the proved private helpers of
-- SquareZeroTensorSectionProductComparison; no multiplication-of-sections theorem is used.

end
end AlgebraicGeometry.Scheme.Modules
