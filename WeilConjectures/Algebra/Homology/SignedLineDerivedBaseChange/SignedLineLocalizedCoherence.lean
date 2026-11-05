/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import all WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineOrdinaryConstraints
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Coherence of localized normalized line comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Reuse tagged equalities when specializing the localization constraints.
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso monoidalCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] KFlatFixedTensor.derivedTensor
  KFlatFixedTensor.selectedTensorPresentation
  KFlatFixedTensor.selectedResolvingTensorPresentation

attribute [local irreducible] derivedLine
  siteSheafTensorRight
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.leftAdjoint
    Functor.rightAdjoint

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

section Abstract
universe ua va ub vb
variable {A₀ : Type ua} {B₀ : Type ub} [Category.{va} A₀] [Category.{vb} B₀]
  (L : A₀ ⥤ B₀) (W : MorphismProperty A₀) [L.IsLocalization W]
include W

end Abstract

section LocalizedUnit
universe a₁ h₁ a₂ h₂ a₃ h₃ a₄ h₄
variable {A₁ : Type a₁} {A₂ : Type a₂} {A₃ : Type a₃} {A₄ : Type a₄}
  [Category.{h₁} A₁] [Category.{h₂} A₂] [Category.{h₃} A₃] [Category.{h₄} A₄]

end LocalizedUnit

section ComplexConstraints
universe ac hc
variable {AA : Type ac} [Category.{hc} AA] [HasZeroMorphisms AA]
end ComplexConstraints
section ComplexCoherence
universe ac hc bc kc
variable {AA : Type ac} [Category.{hc} AA] [HasZeroMorphisms AA]

universe da dah db dbh

end ComplexCoherence
attribute [local irreducible] DerivedCategory.Q
  MorphismProperty.HasLocalization.L MorphismProperty.Q'
  DerivedCategory HomologicalComplex.quasiIso

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

attribute [local irreducible] signedLinePower scalarTensorPower homObj unit

end SheafOfModules.SignedLineDerivedBaseChange
