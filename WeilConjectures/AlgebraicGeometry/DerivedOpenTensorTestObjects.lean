/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedOpenTestObject
import WeilConjectures.AlgebraicGeometry.DerivedOpenTensorHomBijective

/-! # Tensor-stable test objects for derived open restriction
Source: Stacks Project, Tags 00A7, 08BT and 06YB.
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048

/-- Every object on an open admits an extended test object on the ambient scheme,
from which restriction is bijective on Hom sets, also after tensoring.
Source: Stacks Project, Tags 00A7, 08BT and 06YB. -/
theorem exists_derivedOpen_tensorTestObject
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ A : schemeDerivedCategory U.toScheme,
      ∃ B : schemeDerivedCategory X, Nonempty (A ≅ R.obj B) ∧
        (∀ E : schemeDerivedCategory X,
          Function.Bijective (fun f : B ⟶ E ↦ R.map f)) ∧
        (∀ L E : schemeDerivedCategory X,
          Function.Bijective (fun f : B ⊗ L ⟶ E ↦ R.map f)) := by
  dsimp
  intro A
  obtain ⟨B, hAB, hBE⟩ := exists_derivedOpen_testObject X U A
  exact ⟨B, hAB, hBE, derivedOpen_tensorHom_bijective X U B hBE⟩

end AlgebraicGeometry.Scheme
