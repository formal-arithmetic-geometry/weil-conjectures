/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels

/-!
# Strict truncation maps between extensions from coefficient levels

Source: Zheng, Construction 4.1, p. 21, truncation inclusions in the explicit formula.
(blueprint: lem-pur-coefficient-evaluation-strict-sigma).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u v w a b
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Generic
variable {B : ℕ → Sheaf J CommRingCat.{w}}
  {φ : ∀ {m n : ℕ} (_h : n ≤ m), B m ⟶ B n}
  {Syst : Type a} [Category.{b} Syst]
  {ev : ∀ n, Syst ⥤ ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n))}
local notation "tensor" => fun {m n : ℕ} (h : n ≤ m) ↦ siteCoefficientTensor (φ h)
local notation "tensorAdj" => fun {m n : ℕ} (h : n ≤ m) ↦ siteCoefficientTensorAdj (φ h)

end Generic

variable {O : Type w} [CommRing O] {ell : O}

end SheafOfModules
