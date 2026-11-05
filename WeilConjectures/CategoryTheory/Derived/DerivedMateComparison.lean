/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Representative comparison for derived adjunction mates

Source: Stacks 0FND and 09T5.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv c cv d dv a' av' b' bv' c' cv' d' dv'
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {AD : Type a'} [Category.{av'} AD] {BD : Type b'} [Category.{bv'} BD]
  {CD : Type c'} [Category.{cv'} CD] {DD : Type d'} [Category.{dv'} DD]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {LD₁ : AD ⥤ BD} {RD₁ : BD ⥤ AD} {LD₂ : CD ⥤ DD} {RD₂ : DD ⥤ CD}
  {G : A ⥤ C} {H : B ⥤ D} {GD : AD ⥤ CD} {HD : BD ⥤ DD}
  {QA : A ⥤ AD} {QB : B ⥤ BD} {QC : C ⥤ CD} {QD : D ⥤ DD}

end CategoryTheory
