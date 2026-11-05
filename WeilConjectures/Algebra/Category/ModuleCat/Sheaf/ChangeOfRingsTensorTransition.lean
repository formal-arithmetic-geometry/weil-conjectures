/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition
public import WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification

/-!
# Change of rings as a tensor product, and its transition maps

For a morphism `φ : R ⟶ S` of sheaves of commutative rings and a sheaf of `R`-modules `M`,
the change of rings `S ⊗_R M`, regarded as an `R`-module, is the sheaf tensor product
`M ⊗_R S`. Under this identification the transition `s ⊗ m ↦ β s ⊗ m` between changes of
rings is the tensor product of `M` with the coefficient map.

Source: Stacks Project, Tag 03EK.
-/

public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings

namespace SheafOfModules

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

open RestrictedTensorProof

attribute [local implicit_reducible] SheafOfModules.restrictScalars SheafOfModules.unit
  CategoryTheory.sheafCompose siteSheafTensorRight

attribute [local irreducible] changeOfRingsTensorIso swapSheafIso
  siteSheafTensorRightIso tensorObjIsoSheafification

end SheafOfModules
