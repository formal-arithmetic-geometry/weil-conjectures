/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-zero)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local instance] Sheaf.monoidalCategory

local instance (priority := 4000) (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} T
local instance (priority := 4000) (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} T
local instance (priority := 4000) (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} T

private theorem scalarExtensionSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] scalarExtensionSmall

set_option maxHeartbeats 2000000 in
-- The section calculation unfolds both module sheafification and scalar-extension transports.
end AlgebraicGeometry.Scheme.PurityIntegralTower
