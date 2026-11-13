/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnit

/-!
# Open restriction and pullback units

## References

* [Stacks, Cohomology on Sites, Tag 03F3]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pulling back a section along the restriction of a morphism to an open is pulling
back along the original morphism, under the canonical restriction comparisons
(Stacks, Tag 03F3). -/
theorem open_restriction_pullback_unit {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (morphismRestrict g W)).unit.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} W.ι).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 W.toScheme))) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} (morphismRestrict g W)).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} W.ι).obj F)).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift (morphismRestrict g W) (𝟙 (g ⁻¹ᵁ W).toScheme)
            ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp) :
          Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (morphismRestrict g W)).obj
              (Scheme.Etale.mk (𝟙 W.toScheme))).op ≫
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} (morphismRestrict g W) W.ι).inv.app F ≫
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
            (morphismRestrict g W ≫ W.ι) (morphismRestrict_ι g W)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))) ≫
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι
          inferInstance).hom.app ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).obj.map
        (MorphismProperty.Over.homMk (𝟙 (g ⁻¹ᵁ W).toScheme)
          ((Category.id_comp _).trans (Category.id_comp _)) :
          Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶
            (MorphismProperty.Over.map ⊤ (inferInstance : Etale (g ⁻¹ᵁ W).ι)).obj
              (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))).op =
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.ι
          inferInstance).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 W.toScheme))) ≫
      F.obj.map
        (MorphismProperty.Over.homMk (𝟙 W.toScheme)
          ((Category.id_comp _).trans (Category.id_comp _)) :
          Scheme.Etale.mk W.ι ⟶
            (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).obj
              (Scheme.Etale.mk (𝟙 W.toScheme))).op ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app
        (op (Scheme.Etale.mk W.ι)) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift (morphismRestrict g W) (g ⁻¹ᵁ W).ι (morphismRestrict_ι g W))
          (by simp) :
          Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk W.ι)).op := by
  let p : W.toScheme ⟶ X := W.ι
  let p' : (g ⁻¹ᵁ W).toScheme ⟶ Y := (g ⁻¹ᵁ W).ι
  let g' := morphismRestrict g W
  let ι := pullback.lift g' p' (morphismRestrict_ι g W)
  have hι : IsIso ι := by
    have he : (isPullback_morphismRestrict g W).isoPullback.hom = ι := by
      apply pullback.hom_ext <;> simp [ι, g', p']
    rw [← he]
    infer_instance
  let _ : IsIso ι := hι
  have hι₁ : ι ≫ pullback.fst p g = g' := by simp [ι, p, g']
  have hι₂ : ι ≫ pullback.snd p g = p' := by simp [ι, p, p']
  have h := etale_restriction_pullback_unit g p g' p' (by simp [p, p', g']) ι hι₁ hι₂
  obtain ⟨hp', h⟩ := h
  convert h F using 1 <;>
    simp [p, p', g', ι, MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
    MorphismProperty.Comma.isoFromComma, CategoryTheory.Comma.isoMk,
    MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.homMk,
    CategoryTheory.Over.homMk] <;> rfl

end AlgebraicGeometry
