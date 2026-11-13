/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsExistence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsUniqueness

/-!
# Existence and uniqueness of the finite étale trace

## References

* Stacks Project, Tag 03SH
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The unique family of finite étale trace morphisms, natural in the abelian sheaf,
compatible with étale localization, and equal to the sum of restrictions for every finite
clopen splitting (including the empty splitting).
(Stacks, Section 03SH, after Definition 03SE.) -/
theorem existsUnique_finiteEtaleTrace :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f) (W : X.Etale) ↦
      (MorphismProperty.Over.map ⊤ hf).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    let T := ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : Etale f)
      (F : Sheaf X.smallEtaleTopology A),
      (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F
    ∃! tr : T,
      let bar := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) ↦
        (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
            (tr X Y f hfin hf F).hom.app (op W)
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F G : Sheaf X.smallEtaleTopology A) (φ : F ⟶ G),
        tr X Y f hfin hf F ≫ φ =
          (lowerStar A f).map ((upperStar A f).map φ) ≫ tr X Y f hfin hf G) ∧
      (∀ (X Y X' : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (g : X' ⟶ X) (hg : Etale g) (F : Sheaf X.smallEtaleTopology A),
        letI := hfin
        letI := hf
        let f' := pullback.snd f g
        let hf' : Etale f' := inferInstance
        let F' := (upperStar A g).obj F
        ∀ (W : X'.Etale)
          (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
            B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
          κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
          κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
            pullback.snd W.hom f' ≫ pullback.fst f g →
          bar f' inferInstance hf' F' W ≫
              ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app (op W) =
            ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
                (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
              bar f hfin hf F ((MorphismProperty.Over.map ⊤ hg).obj W)) ∧
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y) (t : ∀ j, X ⟶ V j)
          (_ : IsColimit (Cofan.mk Y i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
          (_ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j))
          (_ : ∀ j, IsClosedImmersion (i j))
          (W : X.Etale),
          bar f hfin hf F W = ∑ j, F.obj.map (MorphismProperty.Over.homMk
            (A := W) (B := B f hf W)
            (pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)
              (by simp [Category.assoc, hinv₁]))
            (by simp [B, Category.assoc, hinv₁])).op) := by
  have he := finiteEtaleTrace_exists
  have hu := finiteEtaleTrace_unique
  rcases he with ⟨tr, htr⟩
  exact ⟨tr, htr, fun tr' h' => (hu tr tr' htr h').symm⟩

end AlgebraicGeometry.Etale
