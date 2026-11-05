/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
    WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel

/-! # Ordinary presentations of the constant comparisons

The constant comparisons of `lisseTower_constant_complex_comparisons` are exact
localizations of ordinary comparisons. This file records the natural constant model
and the ordinary natural isomorphisms represented by all derived comparisons involved.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY; Derived Categories, Tag 05RU.
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section Model

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
/- The comparison `presentationPullIso`, for the canonical module inverse-image adjunction
`proEtaleRingModuleAdjunction`, which is uniquely normalized on unit sections. -/

/- `presentationPullIso`, for the canonical module inverse-image adjunction. -/

/- The identity comparison of constant presheaves with identically restricted scalars. -/

/- `presentationTransportIso`, with its presheaf comparison named. -/

/- The identity comparison of the two constant presheaf constructions. -/

/- `sourcePresentationIso`, built from named pieces. -/

/- `ordinaryConstantModel`, for the canonical module inverse-image adjunction. -/

/- `derivedConstantModel`, for the canonical module inverse-image adjunction. -/

end Model

section Paste

variable {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ E : Type*}
  [Category A₀] [Category A₁] [Category B₀] [Category B₁]
  [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁]
  [Abelian C₀] [Abelian C₁] [Abelian D₀] [Abelian D₁] [Abelian E]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory B₀]
  [HasDerivedCategory B₁] [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory E]
  {R : DerivedCategory A₀ ⥤ DerivedCategory A₁} {S : DerivedCategory B₀ ⥤ DerivedCategory
      B₁}
  {T : DerivedCategory C₀ ⥤ DerivedCategory C₁}
  {F₀ : DerivedCategory A₀ ⥤ DerivedCategory B₀} {F₁ : DerivedCategory A₁ ⥤
      DerivedCategory B₁}
  {G₀ : DerivedCategory B₀ ⥤ DerivedCategory C₀} {G₁ : DerivedCategory B₁ ⥤
      DerivedCategory C₁}
  {L₀ : DerivedCategory C₀ ⥤ DerivedCategory D₀} {L₁ : DerivedCategory C₁ ⥤
      DerivedCategory D₁}
  {H₀ : DerivedCategory D₀ ⥤ DerivedCategory E} {H₁ : DerivedCategory D₁ ⥤
      DerivedCategory E}
  {r : A₀ ⥤ A₁} {s : B₀ ⥤ B₁} {t : C₀ ⥤ C₁} {f₀ : A₀ ⥤ B₀} {f₁ : A₁
      ⥤ B₁}
  {g₀ : B₀ ⥤ C₀} {g₁ : B₁ ⥤ C₁} {l₀ : C₀ ⥤ D₀} {l₁ : C₁ ⥤ D₁} {h₀
      : D₀ ⥤ E} {h₁ : D₁ ⥤ E}
  [r.Additive] [s.Additive] [t.Additive] [f₀.Additive] [f₁.Additive] [g₀.Additive]
  [g₁.Additive] [l₀.Additive] [l₁.Additive] [h₀.Additive] [h₁.Additive]

end Paste

section Scalar

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

end Scalar

section Right

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
attribute [local instance] CompletedConstantReduction.constant_additive

end Right

end AlgebraicGeometry.Scheme
