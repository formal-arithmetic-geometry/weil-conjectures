/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Scalar.ScalarTensorTowerComparison

/-! # Internal Hom and arbitrary changes of ring-sheaf coefficients

The scalar comparison is constructed from the five canonical Hom bijections.
Its evaluation and uniqueness follow from the scalar triangle identity;
restriction is conservative by its cohomology comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
variable {J} {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

end SheafOfModules

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
  coefficientTotalTensor CoefficientTensorModels.iso
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

variable {J} {R S T : Sheaf J CommRingCat.{max c v r}}

end CategoryTheory
