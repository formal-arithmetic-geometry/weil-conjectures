/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalization of the completed regular Koszul unit

Source: Stacks Project, Tags 03EK and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero

-- Fix the coefficient universe for the polymorphic sheafification instances.

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

section ScalarUnit
variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)

end ScalarUnit

-- Carry out the scalar-extension calculation with symbolic coefficient rings.
-- This keeps elaboration from unfolding the concrete inverse-limit coefficient ring.

attribute [local irreducible] completedAdicRing completedAdicChangeData

@[irreducible] private def completedRegularUnitIso :
    SheafOfModules.unit (completedAdicRing T d) ≅
      (koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d).obj
        (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)) := by
  let R := adicModuleRing T A
  let G := completedAdicScalarExtension T d
  let hG := (completedAdicScalarExtensionData T d).choose_spec.choose
  let : IsIso (koszulConstantOne T A) := koszulConstantOne_isIso T A
  exact
    (scalarUnitIso (completedAdicScalar T d)).symm ≪≫
      eqToIso (hG (SheafOfModules.unit R)).symm ≪≫
        G.mapIso (asIso (koszulConstantOne T A))

end AlgebraicGeometry.Scheme
