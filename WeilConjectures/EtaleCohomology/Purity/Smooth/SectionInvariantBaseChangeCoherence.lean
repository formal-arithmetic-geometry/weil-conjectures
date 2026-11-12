/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalPasteHoriz
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange

/-!
# Coherence of the base change of section invariants

In a cartesian square `hV ≫ g = g' ≫ h` with compatible sections `s` and `s'`, the base change
isomorphism `Lh^* 𝒞(g, s) ≅ 𝒞(g', s')` of section invariants
(`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`) respects identities and composition of
cartesian squares (blueprint `lemma-naturality-under-base-change-etale` (8)).

## Main statements

- `AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso_id`
- `AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso_paste_horiz`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section BaseChange

/-- Blueprint `lemma-naturality-under-base-change-etale` (8), identities: the base change
isomorphism of section invariants along the identity square is `L(𝟙)^* ≅ 𝟭`. -/
theorem sectionInvariantBaseChangeIso_id {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [IsIso (dualizingComplexBaseChangeMap Λ (IsPullback.id_horiz f))]
    (s : Y ⟶ X) :
    (sectionInvariantBaseChangeIso Λ (IsPullback.id_horiz f) s s (by simp)).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).hom.app (sectionInvariant Λ f s) := by
  sorry

variable {X X' X'' Y Y' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
  {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v₀ : Y'' ⟶ Y} {v' : X' ⟶ X} {w' : X'' ⟶ X'} {v₀' : X'' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
  [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']

/-- Blueprint `lemma-naturality-under-base-change-etale` (8), composition: for cartesian squares
`sq₁ : v' ≫ f = f' ≫ v` and `sq₂ : w' ≫ f' = f'' ≫ w` side by side, with outer square `sq₃`
along `v₀ = w ≫ v`, the base change isomorphism of section invariants along `sq₃` is `Lw^*` of
the one along `sq₁` followed by the one along `sq₂`. -/
theorem sectionInvariantBaseChangeIso_paste_horiz
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) (sq₃ : IsPullback v₀' f'' f v₀)
    (hv : v₀ = w ≫ v) (hv' : v₀' = w' ≫ v')
    [IsIso (dualizingComplexBaseChangeMap Λ sq₁)] [IsIso (dualizingComplexBaseChangeMap Λ sq₂)]
    [IsIso (dualizingComplexBaseChangeMap Λ sq₃)]
    (s : Y ⟶ X) (s' : Y' ⟶ X') (s'' : Y'' ⟶ X'') (hs₁ : s' ≫ v' = v ≫ s)
    (hs₂ : s'' ≫ w' = w ≫ s') (hs₃ : s'' ≫ v₀' = v₀ ≫ s) :
    (sectionInvariantBaseChangeIso Λ sq₃ s s'' hs₃).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w v v₀ hv).hom.app _ ≫
        (L((w)^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantBaseChangeIso Λ sq₁ s s' hs₁).hom ≫
        (sectionInvariantBaseChangeIso Λ sq₂ s' s'' hs₂).hom := by
  sorry

end BaseChange

end Etale

end AlgebraicGeometry
