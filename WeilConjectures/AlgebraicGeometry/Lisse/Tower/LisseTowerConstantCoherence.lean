/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel

/-! # Coherence of the ordinary constant comparisons

The ordinary constant comparisons are compatible with restriction of coefficients along
consecutive quotients; localization gives the coherence of the derived comparisons.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Derived Categories, Tag 05RU.
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace CategoryTheory

section ConstantUnit

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {D B : Type*} [Category* D] [Category* B] (U : D ⥤ B) [HasWeakSheafify J D]
  [HasWeakSheafify J B] [J.PreservesSheafification U] [J.HasSheafCompose U]

end ConstantUnit

section Glue

variable {C₀ C₁ E₀ E₁ P₀ P₁ T₀ T₁ Z₀ Z₁ W₀ W₁ V A' : Type*}
  [Category C₀] [Category C₁] [Category E₀] [Category E₁] [Category P₀] [Category P₁]
  [Category T₀] [Category T₁] [Category Z₀] [Category Z₁] [Category W₀] [Category W₁]
  [Category V] [Category A']
  {R : C₀ ⥤ C₁} {sE : E₀ ⥤ E₁} {sP : P₀ ⥤ P₁} {sT : T₀ ⥤ T₁} {sZ : Z₀ ⥤
      Z₁}
  {CE₀ : C₀ ⥤ E₀} {CE₁ : C₁ ⥤ E₁} {CP₀ : C₀ ⥤ P₀} {CP₁ : C₁ ⥤ P₁}
  {CT₀ : C₀ ⥤ T₀} {CT₁ : C₁ ⥤ T₁} {CZ₀ : C₀ ⥤ Z₀} {CZ₁ : C₁ ⥤ Z₁}
  {cu₀ : E₀ ⥤ P₀} {cu₁ : E₁ ⥤ P₁} {ua₀ : P₀ ⥤ T₀} {ua₁ : P₁ ⥤ T₁}
  {ub₀ : T₀ ⥤ Z₀} {ub₁ : T₁ ⥤ Z₁} {F₀ : Z₀ ⥤ W₀} {F₁ : Z₁ ⥤ W₁}
  {Rq : W₀ ⥤ W₁} {H₀ : W₀ ⥤ V} {H₁ : W₁ ⥤ V}
  {Q₀ : C₀ ⥤ W₀} {Q₁ : C₁ ⥤ W₁} {Af₀ : C₀ ⥤ A'} {Af₁ : C₁ ⥤ A'} {Fin :
      A' ⥤ V}

end Glue

section Glue4

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {RA R₁ R₀ : Sheaf J RingCat.{u + 1}} (p₁ : RA ⟶ R₁) (p₀ : RA ⟶ R₀) (qt : R₁ ⟶
      R₀)

end Glue4

end CategoryTheory

namespace AlgebraicGeometry.Scheme

section Layers

/- The constant inverse-image comparison is characterized by its adjunct. -/

/- Constants pulled back along `f` are compatible with restriction of coefficients. -/

/- Adjuncts and the comparison of right adjoints. -/

/- The comparison of constants is characterized by its adjunct. -/

end Layers

section Realization

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

/- The pulled-back constant section of a constant module sheaf. -/

/- Maps out of a pulled-back constant module sheaf are determined by the pulled-back
constant sections. -/

/- The realization section of a fixed-coefficient section. -/

/- Forgetting the realized module structure returns the original section. -/

/- Pulled-back constant sections are natural in the module. -/

/- The restriction/pullback comparison sends pulled-back sections to pulled-back sections. -/

/- Sections of a sheaf with restricted coefficients. -/

/- Chaining four elementwise equations. -/
private theorem chain4_eq {α β γ δ ε : Type*} {f₁ : α → β} {f₂ : β → γ} {f₃ : γ
    → δ}
    {f₄ : δ → ε} {x : α} {a : β} {b : γ} {c : δ} {y : ε} (h₁ : f₁ x = a) (h₂ :
        f₂ a = b)
    (h₃ : f₃ b = c) (h₄ : f₄ c = y) : f₄ (f₃ (f₂ (f₁ x))) = y := by
  rw [h₁, h₂, h₃, h₄]

/- The constant section over the base-changed terminal object. -/

/- The constant compositor sends constant sections to constant sections. -/

/- The constant presentation section. -/

/- The fixed-coefficient comparison of constant presentations on sections. -/

/- The constant presentation section on the base. -/

/- The pulled-back constant presentation comparison on sections. -/

/- Elementwise naturality of the module sheafification unit. -/

/- The raw coefficient comparison on unit sections. -/

/- Transport of constant presentations sends unit sections to unit sections. -/

/- The source presentation comparison on sections. -/

/- The fixed realization section of a section. -/

/- The pulled-back constant section of a constant quotient module. -/

/- Realization sections are natural. -/

/- Fixed realization sections are natural. -/

/- The constant compositor is compatible with the fixed realization sections. -/

/- Evaluation of a composite on elements. -/

/- The fixed restriction forgetful comparison is the identity on sections. -/

/- The normalized scalar square sends fixed realization sections to fixed realization
sections. -/

/- The restriction compositor is the identity on sections. -/

/- The ordinary constant model sends constant sections to pulled-back constant sections. -/

/- The right square sends pulled-back constant sections to pulled-back constant sections. -/

/- Restriction of scalars along consecutive quotients is the identity on sections. -/

end Realization

section Coherence

variable {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] CompletedConstantReduction.constant_additive

/- The realization layer of the coherence: the constant realization comparisons at levels
`n` and `n + 1` are compatible with the normalized scalar square, the restriction
compositors and the constant quotient comparisons. -/

end Coherence

end AlgebraicGeometry.Scheme
