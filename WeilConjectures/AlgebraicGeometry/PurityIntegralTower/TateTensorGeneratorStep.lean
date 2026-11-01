/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-step)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local instance] Sheaf.monoidalCategory
private instance smallSite (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt
attribute [local instance 2000] tensorModules
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
open scoped TensorProduct ChangeOfRings

private def extensionIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) :
    (pbcExtend φ).obj M ≅ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
  eqToIso ((pbcExtensionExistence φ).choose_spec.choose M)

section RootContraction

attribute [local semireducible] SheafOfModules.monoidalCategory

end RootContraction

set_option maxHeartbeats 1200000 in
-- The coefficient presentations require additional definitional equality checking.
end AlgebraicGeometry.Scheme.PurityIntegralTower
