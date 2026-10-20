/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.RingedTopoiTensorSections
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Termwise scalar extension of ringed-site complexes

Source: Stacks Project, Algebraization, Tag 099I; Modules on Sites, Tag 03D7.
(blueprint: def-weil-pbc-ringed-scalar-extension-complex-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace CategoryTheory

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor Adjunction.mapHomologicalComplex

/-- Scalar extension is additive, by its adjunction to restriction of scalars.
Source: Stacks Project, Tag 03D7.
(blueprint: def-weil-pbc-ringed-scalar-extension-complex-adjunction). -/
instance scalarExtension_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).Additive :=
  (SheafOfModules.RingedTensor.tensorAdjunction φ).left_adjoint_additive

/-- The termwise scalar-extension adjunction on complexes.
Source: Stacks Project, Tag 099I.
(blueprint: def-weil-pbc-ringed-scalar-extension-complex-adjunction). -/
@[irreducible] noncomputable def ringedScalarExtensionComplexAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).mapHomologicalComplex (.up ℤ) ⊣
      (SheafOfModules.RingedTensor.restriction φ).mapHomologicalComplex (.up ℤ) :=
  (SheafOfModules.RingedTensor.tensorAdjunction φ).mapHomologicalComplex (.up ℤ)

end CategoryTheory
