/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Germ
public import WeilConjectures.WeilSheaf.Fourier

/-!
# Inertia at infinity acts on the Artin–Schreier sheaf through a character of order `p`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

section Translation

variable (l) in
/-- The translations of `ĀS_* ℚ̄_ℓ` compose: `σ_c ≫ σ_d = σ_{d + c}`. On sections they are the
pullbacks of functions along `(u, x) ↦ (u, σ̄_c x)`. -/
lemma artinSchreierTranslationSheafHom_hom_comp (c d : k₀) :
    (artinSchreierTranslationSheafHom l c).hom ≫ (artinSchreierTranslationSheafHom l d).hom =
      (artinSchreierTranslationSheafHom l (d + c)).hom := by
  ext U : 3
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    artinSchreierTranslationSheafHom_hom_app, artinSchreierTranslationSheafHom_hom_app,
    artinSchreierTranslationSheafHom_hom_app, ← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp
  · simp [affineLine.geometricTranslationIso_hom_comp]

variable (l) in
/-- The evaluation `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the section `x ↦ (x, σ̄_c x)`, on underlying
sheaves: the pullback of `σ_c` followed by the counit of `ĀS^* ⊣ ĀS_*`. -/
lemma affineLine.artinSchreierEvalHom_hom (c : k₀) :
    (affineLine.artinSchreierEvalHom l c).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map (artinSchreierTranslationSheafHom l c).hom ≫
        (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).counit.app
          (ProEtale.adicConstantSheaf l Ā) := by
  rw [affineLine.artinSchreierEvalHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
  erw [Adjunction.modAdjunction_counit_app_hom]
  rfl

variable (l) in
/-- The translation `σ_c` of `ĀS_* ℚ̄_ℓ` is the pushforward of `ℚ̄_ℓ ≅ σ̄_{c*} ℚ̄_ℓ` followed by
`ĀS_* σ̄_{c*} ≅ ĀS_*`. -/
lemma artinSchreierTranslationSheafHom_hom_eq (c : k₀) :
    (artinSchreierTranslationSheafHom l c).hom =
      (ĀS)_*[WeilCoefficients.{u} l].map
          (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom) ≫
        (ProEtale.lowerStarFactor (WeilCoefficients.{u} l)
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          (ProEtale.adicConstantSheaf l Ā) := by
  rw [artinSchreierTranslationSheafHom_hom, ← ProEtale.lowerStarComp_trans_lowerStarCongr]
  rfl

variable (l) in
/-- **Translating the evaluations.** For the deck transformation `g = σ̄_c` of `ĀS`, with
`g ≫ ĀS = ĀS`, the evaluation along `x ↦ (x, σ̄_{c + d} x)` is the pullback along `g` of the
evaluation along `x ↦ (x, σ̄_d x)`:
```
  ĀS^* ĀS_* ℚ̄_ℓ ───ev_{c + d}────────────────────────────▶ ℚ̄_ℓ
        │                                                   ▲
        │ ≅                                                 │ ≅
        ▼                                                   │
  g^* ĀS^* ĀS_* ℚ̄_ℓ ───g^* ev_d───▶ g^* ℚ̄_ℓ ─────────────────┘
```
-/
lemma affineLine.artinSchreierEvalHom_hom_add (c d : k₀) :
    (affineLine.artinSchreierEvalHom l (c + d)).hom =
      (ProEtale.upperStarFactor (WeilCoefficients.{u} l)
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā)) ≫
        ((affineLine.geometricTranslationIso k₀ c).hom)^*[WeilCoefficients.{u} l].map
          (affineLine.artinSchreierEvalHom l d).hom ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom := by
  have hc := ProEtale.upperStar_map_lowerStarFactor_comp_counit (WeilCoefficients.{u} l)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom)
  rw [← artinSchreierTranslationSheafHom_hom_eq] at hc
  have n := (ProEtale.upperStarFactor (WeilCoefficients.{u} l)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.naturality
      (X := (ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā))
      (Y := (ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā))
      (artinSchreierTranslationSheafHom l d).hom
  simp only [Functor.comp_map] at n
  rw [affineLine.artinSchreierEvalHom_hom, ← artinSchreierTranslationSheafHom_hom_comp,
    Functor.map_comp, Category.assoc, hc]
  rw [reassoc_of% n, affineLine.artinSchreierEvalHom_hom, Functor.map_comp, Category.assoc]
  rfl

end Translation

end AlgebraicGeometry
