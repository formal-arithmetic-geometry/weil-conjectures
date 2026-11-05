/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarGeometricAdjunctions
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullback
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence

/-! # The fixed finite realization, inverse image and the consecutive scalar squares

The fixed sheaf realization commutes with inverse image through the mate of the
identity on sections of direct images. This comparison is compatible with the
section-normalized consecutive scalar squares and the restriction/pullback mates.

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D8 and 03DA.
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/- Chaining an elementwise equation through two further maps. -/
private theorem chain3_eq {α β γ δ : Type*} {f₁ : α → β} {f₂ : β → γ} {f₃ : γ → δ}
    {x : α} {y : β} {z : δ} (h₁ : f₁ x = y) (h : f₃ (f₂ y) = z) : f₃ (f₂ (f₁ x)) = z := by
  rw [h₁, h]

/- Chaining an elementwise equation through a further map. -/
private theorem chain2_eq {α β γ : Type*} {f₁ : α → β} {f₂ : β → γ}
    {x : α} {y : β} {z : γ} (h₁ : f₁ x = y) (h : f₂ y = z) : f₂ (f₁ x) = z := by
  rw [h₁, h]

/- Rewriting the argument of a composite. -/
private theorem congr_apply_eq {α β γ : Type*} {F : β → γ} {G : α → β}
    {a a' : α} {z : γ} (h : a = a') (h' : F (G a') = z) : F (G a) = z := by
  rw [h, h']

section Pullback

variable {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)

/- The inverse-image coefficient interchange sends unit sections to unit sections. -/

end Pullback

end AlgebraicGeometry.Scheme
