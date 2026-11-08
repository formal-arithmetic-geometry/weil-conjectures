/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

private structure OrdinarySiteData
    (B : ℕ → Sheaf J CommRingCat.{w})
    (φ : ∀ {m n : ℕ} (_h : n ≤ m), B m ⟶ B n)
    (Syst : Type a) [Category.{b} Syst]
    (ev : ∀ n, Syst ⥤ ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n)))
    where
  strictTransition : ∀ {m n} (h : n ≤ m), ev m ⟶ ev n ⋙ restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (φ h))
  transition_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
    (toSheaf _).map ((strictTransition (h₂.trans h₁)).app M) ≫
      (siteScalarUnderlyingIso (φ (h₂.trans h₁))).hom.app ((ev n).obj M) =
    ((toSheaf _).map ((strictTransition h₁).app M) ≫
      (siteScalarUnderlyingIso (φ h₁)).hom.app ((ev m).obj M)) ≫
    ((toSheaf _).map ((strictTransition h₂).app M) ≫
      (siteScalarUnderlyingIso (φ h₂)).hom.app ((ev n).obj M))
  extension : ∀ n, ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n)) ⥤ Syst
  adj : ∀ n, extension n ⊣ ev n
  below : ∀ {n q} (h : q ≤ n), extension n ⋙ ev q ≅ siteCoefficientTensor (φ h)
  above : ∀ n q, n < q → ∀ F, IsZero ((ev q).obj ((extension n).obj F))
  hom_formula : ∀ {n q} (h : q ≤ n) F M (f : (extension n).obj F ⟶ M),
    (siteCoefficientTensorAdj (φ h)).homEquiv F ((ev q).obj M)
      ((below h).inv.app F ≫ (ev q).map f) =
        (adj n).homEquiv F M f ≫ (strictTransition h).app M

end Generic

variable {O : Type w} [CommRing O] {ell : O}

end SheafOfModules
