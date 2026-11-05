/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorHomogeneousKernelAction
import WeilConjectures.AlgebraicGeometry.TensorPullbackPowerAppend
import all WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit

/-! # Coefficient coordinates for homogeneous ideal multiplication

Source: Stacks Project, Tag 09MS, tensor powers in the graded ideal sequence;
Tag 01CD, monoidal pullback of modules.
(blueprint: lem-sc-tensor-ideal-section-coefficient-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] tensorPullback boundaryPullbackComparison
  canonicalTensorBoundaryComparisons tensorIdealSectionMultiply boundarySectionDegreeIso
  boundaryCoefficientDegreeIso boundaryPullbackPowIso boundaryTensorPowIso
  tensorPowAddIso tensorPowMulIso Scheme.IdealSheafData.toModules
noncomputable section

-- The regrouping lemmas below use the proved private tensor-power identities in
-- InvertibleSectionRing and SectionRingVeroneseNumeratorTransition.

end
end AlgebraicGeometry.Scheme.Modules
