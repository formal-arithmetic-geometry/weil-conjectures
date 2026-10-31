/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated

/-! # Restriction of an open-closed presentation to a full subcategory -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures

variable {C : Type u} [Category.{v} C]
  (S : ObjectProperty C) (P : SfRecollementPresentation C)
  (ho : ∀ K : S.FullSubcategory, S (P.openTerm.obj K.obj))
  (hc : ∀ K : S.FullSubcategory, S (P.closedTerm.obj K.obj))

/-- Restrict the given functors and their given maps, without choosing replacements.
Source: blueprint localization, integral full-subcategory passage
(blueprint: lem-sf-recollement-full-subcategory-restriction). -/
def sfRecollementRestriction : SfRecollementPresentation S.FullSubcategory where
  openTerm := S.lift (S.ι ⋙ P.openTerm) ho
  closedTerm := S.lift (S.ι ⋙ P.closedTerm) hc
  counit :=
    { app := fun K ↦ ObjectProperty.homMk (P.counit.app K.obj)
      naturality := by
        intro K L f
        ext
        exact P.counit.naturality f.hom }
  unit :=
    { app := fun K ↦ ObjectProperty.homMk (P.unit.app K.obj)
      naturality := by
        intro K L f
        ext
        exact P.unit.naturality f.hom }

instance [Preadditive C] [P.openTerm.Additive] :
    (sfRecollementRestriction S P ho hc).openTerm.Additive where
  map_add := by intros; ext; exact P.openTerm.map_add

instance [Preadditive C] [P.closedTerm.Additive] :
    (sfRecollementRestriction S P ho hc).closedTerm.Additive where
  map_add := by intros; ext; exact P.closedTerm.map_add

instance (A : Type*) [Ring A] [Preadditive C] [Linear A C]
    [P.openTerm.Additive] [P.openTerm.Linear A] :
    (sfRecollementRestriction S P ho hc).openTerm.Linear A where
  map_smul := by intros; ext; exact P.openTerm.map_smul _ _

instance (A : Type*) [Ring A] [Preadditive C] [Linear A C]
    [P.closedTerm.Additive] [P.closedTerm.Linear A] :
    (sfRecollementRestriction S P ho hc).closedTerm.Linear A where
  map_smul := by intros; ext; exact P.closedTerm.map_smul _ _

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [S.IsTriangulated]

/-- Distinguished completions restrict to a full triangulated subcategory.
Source: blueprint localization, integral full-subcategory passage
(blueprint: lem-sf-recollement-full-subcategory-restriction).
Proof: lift the connecting arrow using fullness, correcting by the inclusion's
shift comparison. The image triangle is the given distinguished triangle. -/
theorem sfRecollementRestriction_distinguished
    (ht : ∀ K, ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C)
    (K : S.FullSubcategory) :
    ∃ δ, Triangle.mk ((sfRecollementRestriction S P ho hc).counit.app K)
      ((sfRecollementRestriction S P ho hc).unit.app K) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := ht K.obj
  let T := sfRecollementRestriction S P ho hc
  let δ' : T.closedTerm.obj K ⟶ (T.openTerm.obj K)⟦(1 : ℤ)⟧ :=
    ObjectProperty.homMk (δ ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app (T.openTerm.obj K))
  refine ⟨δ', ?_⟩
  change S.ι.mapTriangle.obj (Triangle.mk (T.counit.app K) (T.unit.app K) δ') ∈
    distTriang C
  apply isomorphic_distinguished _ hδ
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change P.counit.app K.obj ≫ 𝟙 _ = 𝟙 _ ≫ P.counit.app K.obj; simp)
    (by change P.unit.app K.obj ≫ 𝟙 _ = 𝟙 _ ≫ P.unit.app K.obj; simp)
    (by
      change ((δ ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app (T.openTerm.obj K)) ≫
        (S.ι.commShiftIso (1 : ℤ)).hom.app (T.openTerm.obj K)) ≫
          (shiftFunctor C (1 : ℤ)).map (𝟙 (P.openTerm.obj K.obj)) = 𝟙 _ ≫ δ
      calc
        _ = ((δ ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app (T.openTerm.obj K)) ≫
            (S.ι.commShiftIso (1 : ℤ)).hom.app (T.openTerm.obj K)) ≫ 𝟙 _ :=
          congrArg (fun f ↦ ((δ ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app
            (T.openTerm.obj K)) ≫ (S.ι.commShiftIso (1 : ℤ)).hom.app
              (T.openTerm.obj K)) ≫ f)
            ((shiftFunctor C (1 : ℤ)).map_id (P.openTerm.obj K.obj))
        _ = (δ ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app (T.openTerm.obj K)) ≫
            (S.ι.commShiftIso (1 : ℤ)).hom.app (T.openTerm.obj K) := Category.comp_id _
        _ = δ ≫ ((S.ι.commShiftIso (1 : ℤ)).inv.app (T.openTerm.obj K) ≫
            (S.ι.commShiftIso (1 : ℤ)).hom.app (T.openTerm.obj K)) := Category.assoc _ _ _
        _ = δ ≫ 𝟙 _ := congrArg (fun f ↦ δ ≫ f)
          ((S.ι.commShiftIso (1 : ℤ)).inv_hom_id_app (T.openTerm.obj K))
        _ = δ := Category.comp_id δ
        _ = _ := (Category.id_comp δ).symm)

/-- Cross-object orthogonality restricts by the fully faithful inclusion.
Source: blueprint localization, integral full-subcategory passage
(blueprint: lem-sf-recollement-full-subcategory-restriction).
Proof: use the inclusion Hom equivalence and its shift comparison. -/
theorem sfRecollementRestriction_orthogonality
    (h : ∀ (K M : C) (n : ℤ),
      Subsingleton ((P.openTerm.obj K)⟦n⟧ ⟶ P.closedTerm.obj M))
    (K M : S.FullSubcategory) (n : ℤ) :
    Subsingleton (((sfRecollementRestriction S P ho hc).openTerm.obj K)⟦n⟧ ⟶
      (sfRecollementRestriction S P ho hc).closedTerm.obj M) := by
  let T := sfRecollementRestriction S P ho hc
  have hKM := h K.obj M.obj n
  have : Subsingleton (S.ι.obj ((T.openTerm.obj K)⟦n⟧) ⟶
      S.ι.obj (T.closedTerm.obj M)) :=
    let e := Iso.homCongr ((S.ι.commShiftIso n).app (T.openTerm.obj K))
      (Iso.refl (P.closedTerm.obj M.obj))
    ⟨fun f g ↦ e.injective (@Subsingleton.elim _ hKM (e f) (e g))⟩
  exact S.ι.map_injective.subsingleton

end WeilConjectures
