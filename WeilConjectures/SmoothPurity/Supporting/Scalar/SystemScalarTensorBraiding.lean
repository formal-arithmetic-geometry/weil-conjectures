/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorSignedRepresentatives
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction

/-! # Scalar extension preserves the signed symmetry of coherent systems

Source: Stacks Project, Tag 07A4 and the Koszul sign rules, Tag 0FNG.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
  pullbackTensorBraiding pullbackTensorSignedTotal coefficientTotalTensor
attribute [local implicit_reducible] pullbackTensorSwap
  integralComparisonDerivedSequenceScalar
  ScalarExtensionTower.tensor Functor.mapHomologicalComplex
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

open Opposite ScalarExtensionTower

section Chain
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

end Chain

end WeilConjectures
