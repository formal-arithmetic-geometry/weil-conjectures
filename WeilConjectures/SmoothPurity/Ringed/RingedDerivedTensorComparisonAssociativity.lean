/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonAssociativity
import WeilConjectures.SmoothPurity.Ringed.RingedTensorRepresentativeTransport

/-! # Derived associativity from coherent tensor representatives
Source: Stacks 0FPT, 06YU and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.RingedForgetTensorTransposition
namespace WeilConjectures
attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  coefficientTotalTensor coefficientKFlatInclusion
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTensorGenerator
  CoefficientTensorModels.iso DerivedCategory.Q

section RingedModels
universe c v r d c' v' r' d'
variable {V : Type c} [Category.{v} V] (J : GrothendieckTopology V)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{d} (RingedTensorModules.{c, v, r} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, d} J R))
  (T : CoefficientTensorModels.{r, c, v, d} J R S)
variable {V' : Type c'} [Category.{v'} V'] (J' : GrothendieckTopology V')
  [HasSheafify J' AddCommGrpCat.{max c' v' r'}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max c' v' r'}]
  (R' : Sheaf J' CommRingCat.{max c' v' r'})
  [HasDerivedCategory.{d'} (RingedTensorModules.{c', v', r'} J' R')]
  (SU : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c', v', r', d'} J' R'))
  (TU : CoefficientTensorModels.{r', c', v', d'} J' R' SU)

end RingedModels
end WeilConjectures
