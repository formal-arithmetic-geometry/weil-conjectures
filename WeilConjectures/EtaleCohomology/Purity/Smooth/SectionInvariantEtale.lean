/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality

/-!
# Section invariants along étale maps of pairs

Let `e : V' ⟶ V` be an étale map of pairs over `B`: `g' = e ≫ g` and `s' ≫ e = s` for sections
`s` of `g` and `s'` of `g'`. The section invariants `𝒞(g, s) = Ls^* ω_g` and `𝒞(g', s')` are
identified by composing adjunctions: `R(e ≫ g)_! ≅ Rg_! ∘ Re_!`, and `Re_! ⊣ Le^*` for étale `e`,
so the right adjoint `R(e ≫ g)^!` is `Le^* ∘ Rg^!`. Hence `ω_{g'} ≅ Le^* ω_g`
(`AlgebraicGeometry.Etale.dualizingComplexEtaleIso`), and restricting along `s'` gives
`𝒞(g', s') ≅ 𝒞(g, s)` (`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`, blueprint
`lemma-naturality-under-base-change-etale` (5), (6)).

These identifications respect identities and composition, and they commute with base change
(blueprint `lemma-naturality-under-base-change-etale` (8)).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekEtaleCompIso`: `Le^* ∘ Rg^! ≅ R(e ≫ g)^!` for
  étale `e`.
- `AlgebraicGeometry.Etale.dualizingComplexEtaleIso`: `Le^* ω_g ≅ ω_{e ≫ g}`.
- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso`: `𝒞(e ≫ g, s') ≅ 𝒞(g, s)`.

## Main statements

- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_id`,
  `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_comp`: the étale identifications respect
  identities and composition.
- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_baseChange`: base change commutes with the
  étale identifications.
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

variable {V V' B : Scheme.{u}} (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e]
  [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B) [HasCompactification g]
  [HasCompactification g'] [QuasiCompact g'] (hg : e ≫ g = g')

/-- For an étale `e : V' ⟶ V` and `g' = e ≫ g`, the identification `Le^* ∘ Rg^! ≅ Rg'^!` of right
adjoints obtained by composing adjunctions: `Rg'_! ≅ Rg_! ∘ Re_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`) and `Re_! ⊣ Le^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekEtaleAdjunction`). -/
noncomputable def rightDerivedUpperShriekEtaleCompIso :
    R(g)^![Λ] ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) ≅ R(g')^![Λ] :=
  haveI : HasCompactification (e ≫ g) := .of_eq hg.symm
  haveI : QuasiCompact (e ≫ g) := hg ▸ inferInstance
  conjugateIsoEquiv ((rightDerivedLowerShriekEtaleAdjunction Λ e).comp
      (rightDerivedUpperShriekAdjunction Λ g))
    (rightDerivedUpperShriekAdjunction Λ g')
    (rightDerivedLowerShriekCongrIso Λ hg.symm ≪≫ rightDerivedLowerShriekCompIso Λ e g)

/-- For an étale `e : V' ⟶ V` and `g' = e ≫ g`, the identification `Le^* ω_g ≅ ω_{g'}` of
dualizing complexes obtained by composing the adjunctions `Re_! ⊣ Le^*` and `Rg_! ⊣ Rg^!`. -/
noncomputable def dualizingComplexEtaleIso :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) ≅ dualizingComplex Λ g' :=
  (rightDerivedUpperShriekEtaleCompIso Λ e g g' hg).app (𝟙_ _)

/-- Blueprint `lemma-naturality-under-base-change-etale` (5), (6): for an étale map of pairs
`e : V' ⟶ V`, `g' = e ≫ g`, `s' ≫ e = s`, the identification of section invariants

`𝒞(g', s') = Ls'^* ω_{g'} ≅ Ls'^* Le^* ω_g ≅ Ls^* ω_g = 𝒞(g, s)`

obtained by composing adjunctions (`AlgebraicGeometry.Etale.dualizingComplexEtaleIso`). -/
noncomputable def sectionInvariantEtaleIso (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) :
    sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s :=
  (L((s')^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexEtaleIso Λ e g g' hg).symm ≪≫
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s' e s hs.symm).app _).symm

/-- Blueprint `lemma-naturality-under-base-change-etale` (8), identities: the étale
identification along the identity is the identity. -/
theorem sectionInvariantEtaleIso_id [HasCompactification (𝟙 V)] [QuasiCompact g] (s : B ⟶ V) :
    sectionInvariantEtaleIso Λ (𝟙 V) g g (Category.id_comp g) s s (Category.comp_id s) =
      Iso.refl _ := by
  sorry

/-- Blueprint `lemma-naturality-under-base-change-etale` (8), composition: the étale
identification along a composite `e₁ ≫ e₂` of étale maps of pairs is the composite of the
identifications. -/
theorem sectionInvariantEtaleIso_comp {V'' : Scheme.{u}} (e₁ : V'' ⟶ V')
    [_root_.AlgebraicGeometry.Etale e₁] [HasCompactification e₁] [HasCompactification (e₁ ≫ e)]
    (g'' : V'' ⟶ B) [HasCompactification g''] [QuasiCompact g''] (hg₁ : e₁ ≫ g' = g'')
    (s : B ⟶ V) (s' : B ⟶ V') (s'' : B ⟶ V'') (hs : s' ≫ e = s) (hs₁ : s'' ≫ e₁ = s') :
    sectionInvariantEtaleIso Λ (e₁ ≫ e) g g'' (by rw [Category.assoc, hg, hg₁]) s s''
        (by rw [← Category.assoc, hs₁, hs]) =
      sectionInvariantEtaleIso Λ e₁ g' g'' hg₁ s' s'' hs₁ ≪≫
        sectionInvariantEtaleIso Λ e g g' hg s s' hs := by
  sorry

/-- Blueprint `lemma-naturality-under-base-change-etale` (8), interchange of base change with
an étale map of pairs. Let `e : V' ⟶ V` be an étale map of pairs over `B` (`g' = e ≫ g`,
`s' ≫ e = s`) and `h : B₁ ⟶ B`, with cartesian squares `sq : hV ≫ g = g₁ ≫ h` and
`sq' : hV' ≫ g' = g₁' ≫ h`, an étale map of pairs `e₁ : V₁' ⟶ V₁` over `B₁` with
`e₁ ≫ hV = hV' ≫ e`, and sections `s₁`, `s₁'` compatible with `s`, `s'`. Then the base change
isomorphisms of section invariants carry the étale identification `𝒞(g', s') ≅ 𝒞(g, s)` to the
étale identification `𝒞(g₁', s₁') ≅ 𝒞(g₁, s₁)`. -/
theorem sectionInvariantEtaleIso_baseChange [QuasiCompact g] {V₁ V₁' B₁ : Scheme.{u}}
    (h : B₁ ⟶ B) (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) [HasCompactification g₁]
    [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁'] (hV : V₁ ⟶ V)
    (hV' : V₁' ⟶ V') (sq : IsPullback hV g₁ g h) (sq' : IsPullback hV' g₁' g' h)
    [IsIso (dualizingComplexBaseChangeMap Λ sq)] [IsIso (dualizingComplexBaseChangeMap Λ sq')]
    (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁] [HasCompactification e₁]
    (hg₁ : e₁ ≫ g₁ = g₁') (he : e₁ ≫ hV = hV' ≫ e)
    (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) (s₁ : B₁ ⟶ V₁) (s₁' : B₁ ⟶ V₁')
    (hs₁ : s₁' ≫ e₁ = s₁) (hsV : s₁ ≫ hV = h ≫ s) (hsV' : s₁' ≫ hV' = h ≫ s') :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantEtaleIso Λ e g g' hg s s' hs).hom ≫
        (sectionInvariantBaseChangeIso Λ sq s s₁ hsV).hom =
      (sectionInvariantBaseChangeIso Λ sq' s' s₁' hsV').hom ≫
        (sectionInvariantEtaleIso Λ e₁ g₁ g₁' hg₁ s₁ s₁' hs₁).hom := by
  sorry

end Etale

end Etale

end AlgebraicGeometry
