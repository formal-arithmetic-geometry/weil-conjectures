/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientRoosAugmentation
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionLocalizationAssembly
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Normalized Koszul reconstruction comparison

The strict completed Koszul augmentation and the exact-products Roos comparison
are assembled on K-flat complexes, then descended along localization. The unit
calculation uses the independent characterization of the quotient completion unit.
Source: Stacks Tags 091N, 0941 and 099M.
(blueprint: prop-weil-pbc-koszul-reconstruction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

section HomotopyComparison

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive]
  (K : DerivedCategory B ⥤ DerivedCategory B)
  (RF : DerivedCategory C ⥤ DerivedCategory B)

end HomotopyComparison

attribute [local irreducible] reconstructionHomotopyMap

attribute [local irreducible] completedAdicOrdinaryTower completedAdicReductionData

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
