/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation

/-! # The ordinary scalar evaluation comparison

Source: Stacks 03D7, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
section Ordinary
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
set_option backward.defeqAttrib.useBackward true
universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B F : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
  (α : ∀ n, B n ⟶ F n) (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
  (A : SemilinearSections.ScalarSystems.{c, v, r} J B τ F σ α hα)

end Ordinary
end WeilConjectures
