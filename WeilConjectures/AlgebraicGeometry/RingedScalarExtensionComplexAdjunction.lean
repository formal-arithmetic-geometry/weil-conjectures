/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Termwise scalar extension of ringed-site complexes.

## References

* [Stacks Project, Tag 099I](https://stacks.math.columbia.edu/tag/099I)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace CategoryTheory

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor Adjunction.mapHomologicalComplex

/-- Scalar extension is additive, by its adjunction to restriction of scalars. -/
instance scalarExtension_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).Additive :=
  (SheafOfModules.RingedTensor.tensorAdjunction φ).left_adjoint_additive

/-- The termwise scalar-extension adjunction on complexes. -/
@[irreducible] noncomputable def ringedScalarExtensionComplexAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).mapHomologicalComplex (.up ℤ) ⊣
      (SheafOfModules.RingedTensor.restriction φ).mapHomologicalComplex (.up ℤ) :=
  (SheafOfModules.RingedTensor.tensorAdjunction φ).mapHomologicalComplex (.up ℤ)

end CategoryTheory
