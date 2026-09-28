/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Cardinality of the multicospan of a cover

If the category `C` has fewer than `κ` arrows, for a regular cardinal `κ`, then so does the
walking multicospan `WalkingMulticospan S.shape` indexing the sheaf condition for a cover
`S : J.Cover X`
(`CategoryTheory.GrothendieckTopology.Cover.hasCardinalLT_arrow_walkingMulticospan`).
Together with `CategoryTheory.preservesColimitsOfShape_lim_of_isSeparator`, this shows that
the multiequalizers expressing the sheaf condition commute with `κ`-filtered colimits in a
category with a `κ`-presentable separator.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Cover

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}

/-- If `C` has fewer than `κ` arrows for a regular cardinal `κ`, then so does the walking
multicospan indexing the sheaf condition for a cover `S : J.Cover X`: its objects are the
arrows `S.Arrow` and relations `S.Relation` of the cover. -/
lemma hasCardinalLT_arrow_walkingMulticospan (S : J.Cover X) {κ : Cardinal.{w}}
    [Fact κ.IsRegular] (hC : HasCardinalLT (CategoryTheory.Arrow C) κ) :
    HasCardinalLT (CategoryTheory.Arrow (WalkingMulticospan S.shape)) κ := by
  have hκ : Cardinal.aleph0 ≤ κ := (Fact.out : κ.IsRegular).aleph0_le
  have hObj : HasCardinalLT C κ := hasCardinalLT_of_hasCardinalLT_arrow hC
  have hHom (Y Z : C) : HasCardinalLT (Y ⟶ Z) κ :=
    hC.of_injective (fun f ↦ CategoryTheory.Arrow.mk f) fun f g h ↦ by
      change (CategoryTheory.Arrow.mk f).hom = (CategoryTheory.Arrow.mk g).hom
      congr
  have hL : HasCardinalLT S.Arrow κ :=
    (hasCardinalLT_sigma (fun Y : C ↦ { f : Y ⟶ X // S f }) κ hObj fun Y ↦
      (hHom Y X).of_injective _ Subtype.val_injective).of_surjective
      (fun ⟨Y, f, hf⟩ ↦ ⟨Y, f, hf⟩) fun ⟨Y, f, hf⟩ ↦ ⟨⟨Y, f, hf⟩, rfl⟩
  have hR : HasCardinalLT S.Relation κ :=
    (hasCardinalLT_sigma (fun p : S.Arrow × S.Arrow ↦ Σ Z : C,
        { q : (Z ⟶ p.1.Y) × (Z ⟶ p.2.Y) // q.1 ≫ p.1.f = q.2 ≫ p.2.f }) κ
      (hasCardinalLT_prod hκ hL hL) fun p ↦
        hasCardinalLT_sigma _ κ hObj fun Z ↦
          (hasCardinalLT_prod hκ (hHom _ _) (hHom _ _)).of_injective _
            Subtype.val_injective).of_surjective
      (fun ⟨p, Z, q, w⟩ ↦ ⟨⟨Z, q.1, q.2, w⟩⟩)
      fun ⟨⟨Z, g₁, g₂, w⟩⟩ ↦ ⟨⟨(_, _), Z, (g₁, g₂), w⟩, rfl⟩
  exact Limits.hasCardinalLT_arrow_walkingMulticospan hL hR hκ

end CategoryTheory.GrothendieckTopology.Cover
