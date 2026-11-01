/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ReconstructionUniformTower
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.NormalizedTateTensorTower
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.FinitePuritySourceUnitReduction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Reconstruction of the normalized finite smooth-purity tower

Source: current blueprint, sk-thm-purity-transport, proof Steps 1--2.
(blueprint: lem-pur-condensed-tate-integral-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange

end AlgebraicGeometry.Scheme.PurityIntegralTower
