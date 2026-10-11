/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Composition of coextensions of scalars

For ring morphisms `φ : R₁ →+* R₂`, `ψ : R₂ →+* R₃` and `χ = ψ ∘ φ`, coextension of scalars along
`φ` followed by coextension along `ψ` is coextension along `χ`
(`ModuleCat.coextendScalarsCompIso`): it is the conjugate, under the adjunctions
`restrictScalars ⊣ coextendScalars`, of the identification of restriction of scalars along `χ` with
the composite of restrictions (`ModuleCat.restrictScalarsComp'`). These isomorphisms satisfy the
cocycle condition (`ModuleCat.coextendScalarsCompIso_cocycle`), since the restriction
isomorphisms do and conjugation is compatible with composition and whiskering.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

variable {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]

/-- The adjunction `restrictScalars f ⊣ coextendScalars f` in a single universe. -/
noncomputable abbrev coextendScalarsAdj {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    restrictScalars.{u} f ⊣ coextendScalars.{u, u, u} f :=
  restrictCoextendScalarsAdj.{u} f

/-- Coextension of scalars along `φ` followed by coextension along `ψ` is coextension along
`χ = ψ ∘ φ`. -/
noncomputable def coextendScalarsCompIso (φ : R₁ →+* R₂) (ψ : R₂ →+* R₃) (χ : R₁ →+* R₃)
    (h : χ = ψ.comp φ) :
    coextendScalars.{u, u, u} φ ⋙ coextendScalars.{u, u, u} ψ ≅ coextendScalars.{u, u, u} χ :=
  ((conjugateIsoEquiv (coextendScalarsAdj χ) ((coextendScalarsAdj ψ).comp (coextendScalarsAdj φ)))
    (restrictScalarsComp'.{u} φ ψ χ h).symm).symm

lemma coextendScalarsCompIso_hom (φ : R₁ →+* R₂) (ψ : R₂ →+* R₃) (χ : R₁ →+* R₃)
    (h : χ = ψ.comp φ) :
    (coextendScalarsCompIso φ ψ χ h).hom =
      conjugateEquiv ((coextendScalarsAdj ψ).comp (coextendScalarsAdj φ)) (coextendScalarsAdj χ)
        (restrictScalarsComp'.{u} φ ψ χ h).hom :=
  rfl

/-- The cocycle condition for the composition isomorphisms of coextension of scalars. -/
theorem coextendScalarsCompIso_cocycle (φ₁ : R₁ →+* R₂) (φ₂ : R₂ →+* R₃) (φ₃ : R₃ →+* R₄)
    (φ₁₂ : R₁ →+* R₃) (φ₂₃ : R₂ →+* R₄) (φ₁₃ : R₁ →+* R₄) (h₁₂ : φ₁₂ = φ₂.comp φ₁)
    (h₂₃ : φ₂₃ = φ₃.comp φ₂) (h : φ₁₃ = φ₃.comp φ₁₂) (h' : φ₁₃ = φ₂₃.comp φ₁) :
    Functor.whiskerRight (coextendScalarsCompIso φ₁ φ₂ φ₁₂ h₁₂).hom
        (coextendScalars.{u, u, u} φ₃) ≫ (coextendScalarsCompIso φ₁₂ φ₃ φ₁₃ h).hom =
      Functor.whiskerLeft (coextendScalars.{u, u, u} φ₁)
          (coextendScalarsCompIso φ₂ φ₃ φ₂₃ h₂₃).hom ≫
        (coextendScalarsCompIso φ₁ φ₂₃ φ₁₃ h').hom := by
  rw [coextendScalarsCompIso_hom, coextendScalarsCompIso_hom, coextendScalarsCompIso_hom,
    coextendScalarsCompIso_hom, ← conjugateEquiv_whiskerLeft, ← conjugateEquiv_whiskerRight,
    conjugateEquiv_comp, conjugateEquiv_comp]
  congr 1

end ModuleCat
