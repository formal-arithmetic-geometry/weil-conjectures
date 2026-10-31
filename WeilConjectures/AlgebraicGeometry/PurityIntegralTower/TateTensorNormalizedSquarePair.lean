/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorPairFiniteSquare
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Fixed-pair reduction of the normalized Tate tensor square.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square-pair)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange finiteModelIso

end AlgebraicGeometry.Scheme.PurityIntegralTower
