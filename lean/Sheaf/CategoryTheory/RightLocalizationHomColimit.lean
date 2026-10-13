/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-!
# Morphisms in a right localization as a colimit

Source: Stacks Project, Categories, Remark 4.27.15, Tag 05Q4; Derived Categories,
Tag 0FND (blueprint: lem-pc-right-localization-hom-colimit).
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory

/-- Morphisms in a right localization are the colimit of ordinary Hom sets over
`(W.Over ⊤ M)ᵒᵖ`. Source: Stacks Project, Categories, Tag 05Q4
(blueprint: lem-pc-right-localization-hom-colimit).

The map is characterized on every colimit representative, so it is the canonical map,
not merely an unspecified bijection. `RightFraction.map` is inverse denominator followed
by numerator. `ColimitType` is Mathlib's quotient model of the colimit of sets, allowing
independent universes for the indexing category and the Hom sets.

Proof: precomposition along a commuting triangle preserves the localized fraction,
so the representative formula descends to the colimit. Every localized morphism has
a right-fraction representative (lem-pc-right-fraction-representation), proving
surjectivity. Equal localized fractions admit a common refinement with equal numerators
(lem-pc-right-fraction-common-refinement); the corresponding index morphisms identify
their representatives in the colimit, proving injectivity. These two properties give
bijectivity. For the identity system the formula reduces to the identity on Hom sets. -/
theorem rightLocalization_hom_colimit_bijective
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q' : C ⥤ D) [Q'.IsLocalization W] (M N : C) :
    let F := (MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M).op ⋙ yoneda.obj N
    ∃ g : F.ColimitType → (Q'.obj M ⟶ Q'.obj N),
      Function.Bijective g ∧
        ∀ (t : W.Over ⊤ M) (f : t.left ⟶ N),
          g (F.ιColimitType (Opposite.op t) f) =
            (MorphismProperty.RightFraction.mk t.hom t.prop f).map Q'
              (Localization.inverts Q' W) := by
  let F := (MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M).op ⋙ yoneda.obj N
  let c : F.CoconeTypes :=
    { pt := Q'.obj M ⟶ Q'.obj N
      ι t f := (MorphismProperty.RightFraction.mk t.unop.hom t.unop.prop f).map Q'
        (Localization.inverts Q' W)
      ι_naturality := by
        intro s t a
        funext f
        change (MorphismProperty.RightFraction.mk t.unop.hom t.unop.prop
            (a.unop.left ≫ f)).map Q' (Localization.inverts Q' W) =
          (MorphismProperty.RightFraction.mk s.unop.hom s.unop.prop f).map Q'
            (Localization.inverts Q' W)
        apply (MorphismProperty.RightFraction.map_eq_iff Q' W _ _).mpr
        refine ⟨t.unop.left, 𝟙 _, a.unop.left, ?_, ?_, ?_⟩
        · simpa only [Category.id_comp] using (MorphismProperty.Over.w a.unop).symm
        · simp only [Category.id_comp]
        · simpa only [Category.id_comp] using t.unop.prop }
  refine ⟨F.descColimitType c, ⟨?_, ?_⟩, fun t f ↦ rfl⟩
  · intro x y h
    obtain ⟨s, f, rfl⟩ := F.ιColimitType_jointly_surjective x
    obtain ⟨t, g, rfl⟩ := F.ιColimitType_jointly_surjective y
    change (MorphismProperty.RightFraction.mk s.unop.hom s.unop.prop f).map Q'
        (Localization.inverts Q' W) =
      (MorphismProperty.RightFraction.mk t.unop.hom t.unop.prop g).map Q'
        (Localization.inverts Q' W) at h
    obtain ⟨R, a, b, hs, hf, ha⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff Q' W _ _).mp h
    let r : W.Over ⊤ M := MorphismProperty.Over.mk ⊤ (a ≫ s.unop.hom) ha
    let α : r ⟶ s.unop := MorphismProperty.Over.homMk a rfl
    let β : r ⟶ t.unop := MorphismProperty.Over.homMk b hs.symm
    apply F.ιColimitType_eq_of_map_eq_map f g α.op β.op
    exact hf
  · intro g
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q' W g
    exact ⟨F.ιColimitType (Opposite.op (MorphismProperty.Over.mk ⊤ φ.s φ.hs)) φ.f,
      hφ.symm⟩

end CategoryTheory
