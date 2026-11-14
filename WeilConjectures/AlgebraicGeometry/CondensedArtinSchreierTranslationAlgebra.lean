/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedModulePushforwardMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Deck translations preserve the condensed pushforward algebra -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option quotPrecheck false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
open scoped CategoryTheory.Obj

private theorem abstract_translation_algebra
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : C ⥤ C) (G : C ⥤ D) [H.LaxMonoidal] [G.LaxMonoidal]
    (c : H ⋙ G ⟶ G) [NatTrans.IsMonoidal c] :
    let t := G.map (ε H) ≫ c.app (𝟙_ C)
    (μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom) ≫ t =
      (t ⊗ₘ t) ≫ μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom ∧
      ε G ≫ t = ε G := by
  let t := G.map (ε H) ≫ c.app (𝟙_ C)
  have : IsMonHom t := by dsimp only [t]; infer_instance
  constructor
  · exact IsMonHom.mul_hom t
  · have h := IsMonHom.one_hom t
    change (ε G ≫ G.map (𝟙 (𝟙_ C))) ≫ t = ε G ≫ G.map (𝟙 (𝟙_ C)) at h
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id, t, Category.assoc] using h

namespace AlgebraicGeometry.ProEtale

attribute [local instance] CondensedRing.moduleLowerStarMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]

local notation "A" => AffineSpace PUnit (Spec (CommRingCat.of k))
local notation "R" => Mod.regular (condensedRingObj Λ A)
local notation "q" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)
local notation "G" => CondensedRing.lowerStar Λ q

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
private theorem translation_eq (a : k) :
    (condensedArtinSchreierTranslationAction Λ k a).asHom =
      (CondensedRing.lowerStar Λ q).map
        (ε (CondensedRing.lowerStar Λ (Etale.artinSchreierTranslation k a))) ≫
        ((CondensedRing.lowerStarComp Λ (Etale.artinSchreierTranslation k a) q).hom ≫
          (CondensedRing.lowerStarCongr Λ
            (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)).hom).app (𝟙_ _) := by
  simp only [condensedArtinSchreierTranslationAction, NatTrans.comp_app,
    condensedArtinSchreierPushforward]
  simp only [Mod.tensorUnit_eq_regular]
  simp only [CondensedRing.lowerStarCongr, eqToIso.hom, eqToHom_app]
  congr 2

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
/-- The actual deck translation defining the character projector preserves multiplication
and constant functions in the algebra of the Artin–Schreier pushforward. -/
theorem condensedArtinSchreierTranslation_algebra (a : k) :
    (μ G R R ≫ (CondensedRing.lowerStar Λ q).map
      (Mod.regularMul (condensedRingObj Λ A))) ≫
        (condensedArtinSchreierTranslationAction Λ k a).asHom =
      ((condensedArtinSchreierTranslationAction Λ k a).asHom ⊗ₘ
        (condensedArtinSchreierTranslationAction Λ k a).asHom) ≫
          μ G R R ≫ (CondensedRing.lowerStar Λ q).map
            (Mod.regularMul (condensedRingObj Λ A)) ∧
      ε G ≫ (condensedArtinSchreierTranslationAction Λ k a).asHom = ε G := by
  let σ := Etale.artinSchreierTranslation k a
  let H := CondensedRing.lowerStar Λ σ
  let c : H ⋙ G ⟶ G :=
    (CondensedRing.lowerStarComp Λ σ q).hom ≫
      (CondensedRing.lowerStarCongr Λ
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)).hom
  have := CondensedRing.moduleLowerStarCompIsMonoidal Λ σ q
  have := CondensedRing.moduleLowerStarCongrIsMonoidal Λ
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)
  have : NatTrans.IsMonoidal c := by dsimp only [c]; infer_instance
  have h := abstract_translation_algebra H G c
  simpa only [translation_eq, H, σ, condensedArtinSchreierPushforward,
    Mod.tensorUnit_eq_regular, Mod.regularMul_eq] using h

end AlgebraicGeometry.ProEtale
