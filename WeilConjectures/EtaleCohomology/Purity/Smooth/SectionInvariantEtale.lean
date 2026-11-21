/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality

/-!
# Section invariants along étale maps

Let `e : V' ⟶ V` be étale and `g : V ⟶ B`, `g' = e ≫ g`. Composing the adjunctions
`R(e)_! ⊣ Le^*` (`e` is étale) and `R(g)_! ⊣ Rg^!` and comparing with
`R(g')_! ≅ R(g)_! R(e)_!` identifies the exceptional inverse images,
`Rg'^! ≅ Le^* Rg^!`, hence the dualizing complexes `ω_{g'} ≅ Le^* ω_g`. For sections `s` of `g`
and `s'` of `g'` with `s' ≫ e = s` this gives an identification of section invariants

`𝒞(g', s') = Ls'^* ω_{g'} ≅ Ls'^* Le^* ω_g ≅ Ls^* ω_g = 𝒞(g, s)`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplexEtaleCompIso`: `ω_{g'} ≅ Le^* ω_g`.
- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso`: `𝒞(g', s') ≅ 𝒞(g, s)`.

## Main statements

- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_id`,
  `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_comp`,
  `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_baseChange`: these identifications respect
  identities, composition and base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Etale

variable {V' V B : Scheme.{u}} (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e]
  [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B) (w : e ≫ g = g') [HasCompactification g]
  [HasCompactification g'] [QuasiCompact g']

/-- The identification `Rg'^! ≅ Le^* Rg^!` for `g' = e ≫ g` with `e` étale, conjugate to the
composition isomorphism `R(g')_! ≅ R(g)_! R(e)_!` under the composite adjunction
`R(g)_! R(e)_! ⊣ Le^* Rg^!`. -/
noncomputable def rightDerivedUpperShriekEtaleCompIso :
    R(g')^![Λ] ≅ R(g)^![Λ] ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  (conjugateIsoEquiv ((rightDerivedLowerShriekEtaleAdjunction Λ e).comp
      (rightDerivedUpperShriekAdjunction Λ g)) (rightDerivedUpperShriekAdjunction Λ g')
    (rightDerivedLowerShriekCompIsoOfEq Λ e g g' w)).symm

/-- The identification of dualizing complexes `ω_{g'} ≅ Le^* ω_g` for `g' = e ≫ g` with `e`
étale, obtained by composing adjunctions. -/
noncomputable def dualizingComplexEtaleCompIso :
    dualizingComplex Λ g' ≅ (L((e)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) :=
  (rightDerivedUpperShriekEtaleCompIso Λ e g g' w).app (𝟙_ _)

/-- The identification of section invariants `𝒞(g', s') ≅ 𝒞(g, s)` along an étale `e`, for
`g' = e ≫ g` and sections with `s' ≫ e = s`:
`Ls'^* ω_{g'} ≅ Ls'^* Le^* ω_g ≅ Ls^* ω_g`. -/
noncomputable def sectionInvariantEtaleIso (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) :
    sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s :=
  (L((s')^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexEtaleCompIso Λ e g g' w) ≪≫
    ((leftDerivedUpperStarComp _ s' e s hs.symm).app _).symm

end Etale

section Coherence

variable {V'' V' V B : Scheme.{u}}

/-- The identification of section invariants along the identity is the identity. -/
theorem sectionInvariantEtaleIso_id (g : V ⟶ B) [HasCompactification g] [QuasiCompact g]
    [HasCompactification (𝟙 V)] (s : B ⟶ V) :
    sectionInvariantEtaleIso Λ (𝟙 V) g g (Category.id_comp g) s s (Category.comp_id s) =
      Iso.refl _ := by
  sorry

/-- The identifications of section invariants along étale maps are compatible with
composition. -/
theorem sectionInvariantEtaleIso_comp (e₁ : V'' ⟶ V') (e₂ : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e₁] [_root_.AlgebraicGeometry.Etale e₂]
    [HasCompactification e₁] [HasCompactification e₂] [HasCompactification (e₁ ≫ e₂)]
    (g : V ⟶ B) (g' : V' ⟶ B) (g'' : V'' ⟶ B) (w₂ : e₂ ≫ g = g') (w₁ : e₁ ≫ g' = g'')
    [HasCompactification g] [HasCompactification g'] [HasCompactification g''] [QuasiCompact g']
    [QuasiCompact g''] (s : B ⟶ V) (s' : B ⟶ V') (s'' : B ⟶ V'') (h₂ : s' ≫ e₂ = s)
    (h₁ : s'' ≫ e₁ = s') :
    sectionInvariantEtaleIso Λ (e₁ ≫ e₂) g g'' (by rw [Category.assoc, w₂, w₁]) s s''
        (by rw [← Category.assoc, h₁, h₂]) =
      sectionInvariantEtaleIso Λ e₁ g' g'' w₁ s' s'' h₁ ≪≫
        sectionInvariantEtaleIso Λ e₂ g g' w₂ s s' h₂ := by
  sorry

/-- The identifications of section invariants along étale maps commute with base change: for
`b : B₁ ⟶ B`, base changes `g₁` of `g` and `g₁'` of `g' = e ≫ g`, and the base change `e₁` of
`e`, the base change isomorphisms of section invariants carry the identification along `e` to
the identification along `e₁`. -/
theorem sectionInvariantEtaleIso_baseChange {V₁' V₁ B₁ : Scheme.{u}} (e : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B)
    (w : e ≫ g = g') [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
    (b : B₁ ⟶ B) (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁] [HasCompactification e₁]
    (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) (w₁ : e₁ ≫ g₁ = g₁') [HasCompactification g₁]
    [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁'] (v : V₁ ⟶ V) (v' : V₁' ⟶ V')
    (sq : IsPullback v g₁ g b) (sq' : IsPullback v' g₁' g' b) (hv : v' ≫ e = e₁ ≫ v)
    [IsIso (dualizingComplexBaseChangeMap Λ sq)] [IsIso (dualizingComplexBaseChangeMap Λ sq')]
    (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) (s₁ : B₁ ⟶ V₁) (s₁' : B₁ ⟶ V₁')
    (hs₁ : s₁' ≫ e₁ = s₁) (hv₁ : s₁ ≫ v = b ≫ s) (hv₁' : s₁' ≫ v' = b ≫ s') :
    (sectionInvariantBaseChangeIso Λ sq' s' s₁' hv₁').symm ≪≫
        (L((b)^*[ModuleCat.{u + 1} Λ])).mapIso (sectionInvariantEtaleIso Λ e g g' w s s' hs) ≪≫
        sectionInvariantBaseChangeIso Λ sq s s₁ hv₁ =
      sectionInvariantEtaleIso Λ e₁ g₁ g₁' w₁ s₁ s₁' hs₁ := by
  sorry

end Coherence

end Etale

end AlgebraicGeometry
