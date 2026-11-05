/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
import WeilConjectures.CategoryTheory.Native.NativePrincipalCompletenessSmallModel
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.CategoryTheory.Principal.PrincipalConeSmallSiteCriterion
/-! # Principal cone criterion with independent site and coefficient sizes

Source: Stacks 03A0, 03CH, 03DA, 03DG, 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-native-principal-cone-criterion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxErrors 5
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
set_option hygiene false in
local notation "F" => AsSmall.down.{v, c, max c v r} (C := C)
set_option hygiene false in
local notation "Jsmall" => (F).inducedTopology J
variable [(F).IsEquivalence]
variable (R : Sheaf J CommRingCat.{max c v r})
set_option hygiene false in
local notation "S" => restrictedCommRing.{max c v r, c, max c v r, v, r} (K := Jsmall) F R
set_option hygiene false in
local notation "Rg" => NativeRings.{max c v r, c, v} R
set_option hygiene false in
local notation "Rs" => NativeRings.{max c v r, max c v r, max c v r} S
variable
  [HasSheafify J AddCommGrpCat.{max c v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify Jsmall AddCommGrpCat.{max c v r}] [(Jsmall).WEqualsLocallyBijective
    AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, ((Jsmall).over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) CommRingCat.{max c v r}]
  [HasDerivedCategory.{w} (NativeModules.{max c v r, c, v} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c v r, max c v r, max c v r} S)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U))]
  [∀ U : AsSmall.{max c v r} C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rs).over U))]
attribute [local instance] sliceDense globalModulesEquivalence sliceModulesEquivalence

variable [HasCountableProducts (NativeModules.{max c v r, c, v} R)]
  [HasCountableProducts (NativeModules.{max c v r, max c v r, max c v r} S)]
  [HasExactLimitsOfShape (Discrete ℕ)
    (NativeModules.{max c v r, max c v r, max c v r} S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ NativeModules.{max c v r, max c v r, max c v r} S)]

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit

end CategoryTheory.NativeRestriction
