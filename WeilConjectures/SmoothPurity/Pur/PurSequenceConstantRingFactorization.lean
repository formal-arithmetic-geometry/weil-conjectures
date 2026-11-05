/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantSequenceModuleEquivalenceOfUniverses
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Factoring the ordinary projection through the constant completed ring

Source: Stacks 0940, section-derived-limits, and 03D7, change of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures
open SemilinearSections

section ConstantGeometry
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (A : Sheaf J CommRingCat.{max c v r})

end ConstantGeometry

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

end WeilConjectures
