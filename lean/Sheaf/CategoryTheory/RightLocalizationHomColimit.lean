/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-!
# Morphisms in a right localization as a colimit

Source: Stacks Project, Categories, Remark 4.27.15, Tag 05Q4; Derived Categories,
Tag 0FND (blueprint: lem-pc-right-localization-hom-colimit).
-/

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
  sorry

end CategoryTheory
