/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # The augmented derived tower unit

## Main results

- `CategoryTheory.exists_augmentedDerivedTowerUnit`: the two unique natural lifts and
  their ordinary-unit normalization at every object.
- `CategoryTheory.towerAugmentation_ordinaryUnit`: for strict towers, the ordinary
  unit followed by the limit of the augmentation is the map of its augmentation cone.

The functor `RF` and comparison `γ` are supplied data. The property
`CategoryTheory.IsDerivedLimit` alone does not choose either of them.

## References

* Stacks Project, Tag 099M.
-/

@[expose] public section

universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃

namespace CategoryTheory

/-- The universal right Kan lift and the localization lift give a normalized completion map.
Here `v ≫ whiskerRight t RF` is the natural transformation called `c` in the original
construction. Stacks Project, Tag 099M. -/
theorem exists_augmentedDerivedTowerUnit
    {C₀ : Type u₀} {C₁ : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃}
    [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} D₀] [Category.{v₃} D₁]
    (W : MorphismProperty C₀) (q : C₀ ⥤ D₀) [q.IsLocalization W]
    (q' : C₁ ⥤ D₁) (G T : C₀ ⥤ C₁) (F : C₁ ⥤ C₀)
    (DG LT : D₀ ⥤ D₁) (RF : D₁ ⥤ D₀)
    (ν : 𝟭 C₀ ⟶ G ⋙ F) (η : G ⟶ T) (γ : F ⋙ q ⟶ q' ⋙ RF)
    (α : q ⋙ DG ≅ G ⋙ q') (β : q ⋙ LT ⟶ T ⋙ q') [LT.IsRightKanExtension β] :
    ∃ (t : DG ⟶ LT) (v : 𝟭 D₀ ⟶ DG ⋙ RF),
      (∀ X : C₀, t.app (q.obj X) ≫ β.app X = α.hom.app X ≫ q'.map (η.app X)) ∧
      (∀ t' : DG ⟶ LT,
        (∀ X : C₀, t'.app (q.obj X) ≫ β.app X = α.hom.app X ≫ q'.map (η.app X)) →
        t' = t) ∧
      (∀ X : C₀, v.app (q.obj X) ≫ RF.map (α.hom.app X) =
        q.map (ν.app X) ≫ γ.app (G.obj X)) ∧
      (∀ v' : 𝟭 D₀ ⟶ DG ⋙ RF,
        (∀ X : C₀, v'.app (q.obj X) ≫ RF.map (α.hom.app X) =
          q.map (ν.app X) ≫ γ.app (G.obj X)) → v' = v) ∧
      (∀ X : C₀,
        (v ≫ Functor.whiskerRight t RF).app (q.obj X) ≫ RF.map (β.app X) =
          q.map (ν.app X ≫ F.map (η.app X)) ≫ γ.app (T.obj X)) := by
  let a : q ⋙ DG ⟶ T ⋙ q' := α.hom ≫ Functor.whiskerRight η q'
  let t : DG ⟶ LT := LT.liftOfIsRightKanExtension β DG a
  have ht (X : C₀) :
      t.app (q.obj X) ≫ β.app X = α.hom.app X ≫ q'.map (η.app X) :=
    LT.liftOfIsRightKanExtension_fac_app β DG a X
  let d : q ⟶ q ⋙ (DG ⋙ RF) :=
    (Functor.leftUnitor q).inv ≫ Functor.whiskerRight ν q ≫
      (Functor.associator G F q).hom ≫ Functor.whiskerLeft G γ ≫
      (Functor.associator G q' RF).inv ≫ Functor.whiskerRight α.inv RF ≫
      (Functor.associator q DG RF).hom
  let v : 𝟭 D₀ ⟶ DG ⋙ RF :=
    Localization.liftNatTrans q W q (q ⋙ (DG ⋙ RF)) (𝟭 D₀) (DG ⋙ RF) d
  have hv (X : C₀) : v.app (q.obj X) ≫ RF.map (α.hom.app X) =
      q.map (ν.app X) ≫ γ.app (G.obj X) := by
    simp [v, Localization.liftNatTrans_app, d, Category.assoc, ← RF.map_comp]
  refine ⟨t, v, ht, ?_, hv, ?_, ?_⟩
  · intro t' ht'
    apply LT.hom_ext_of_isRightKanExtension β
    ext X
    exact (ht' X).trans (ht X).symm
  · intro v' hv'
    apply Localization.natTrans_ext q W
    intro X
    apply (cancel_mono (RF.map (α.hom.app X))).mp
    exact (hv' X).trans (hv X).symm
  · intro X
    change (v.app (q.obj X) ≫ RF.map (t.app (q.obj X))) ≫ RF.map (β.app X) = _
    have hγ := γ.naturality (η.app X)
    dsimp only [Functor.comp_map] at hγ
    rw [Category.assoc, ← RF.map_comp, ht, RF.map_comp, ← Category.assoc, hv,
      Category.assoc, ← hγ, ← Category.assoc, ← q.map_comp]

end CategoryTheory
