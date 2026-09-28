/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# `κ`-small limits commute with `κ`-filtered colimits

We show that the limit functor `lim : (K ⥤ Type w) ⥤ Type w` over a category `K` with
`HasCardinalLT (Arrow K) κ` is `κ`-accessible (`CategoryTheory.Functor.isCardinalAccessible_lim`),
i.e. `κ`-small limits of types commute with `κ`-filtered colimits.

More generally, in a balanced category `A` with a `κ`-presentable separator `G`, the limit
functor `lim : (K ⥤ A) ⥤ A` preserves colimits of any `κ`-filtered shape
(`CategoryTheory.preservesColimitsOfShape_lim_of_isSeparator`): the functor
`Hom(G, -)` preserves limits and `κ`-filtered colimits, and reflects isomorphisms, so the
statement reduces to the case of types.
-/

@[expose] public section

universe w v u u' v'

namespace CategoryTheory

open Limits Opposite

section

variable {K : Type u'} [Category.{v'} K] [HasLimitsOfShape K (Type w)]

instance (k : K) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ((evaluation K (Type w)).obj k).IsCardinalAccessible κ where
  preservesColimitOfShape _ := inferInstance

/-- If `HasCardinalLT (Arrow K) κ`, then the limit functor `lim : (K ⥤ Type w) ⥤ Type w` is
`κ`-accessible: `κ`-small limits of types commute with `κ`-filtered colimits. -/
lemma Functor.isCardinalAccessible_lim (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hK : HasCardinalLT (Arrow K) κ) :
    (lim : (K ⥤ Type w) ⥤ Type w).IsCardinalAccessible κ :=
  Functor.isCardinalAccessible_of_isLimit
    (c := ({ pt := lim, π := { app k := { app F := limit.π F k } } } :
      Cone (evaluation K (Type w))))
    (evaluationJointlyReflectsLimits _ fun F ↦ limit.isLimit F) κ hK

end

/-- In a balanced category `A` with a `κ`-presentable separator `G`, the limit functor
`lim : (K ⥤ A) ⥤ A` over a category `K` with `HasCardinalLT (Arrow K) κ` preserves
colimits of any `κ`-filtered shape `J`. -/
lemma preservesColimitsOfShape_lim_of_isSeparator {A : Type u} [Category.{v} A] [Balanced A]
    {G : A} (hG : IsSeparator G) (κ : Cardinal.{v}) [Fact κ.IsRegular] [IsCardinalPresentable G κ]
    (J : Type v) [SmallCategory J] [IsCardinalFiltered J κ] [HasColimitsOfShape J A]
    {K : Type u'} [Category.{v'} K] [HasLimitsOfShape K (Type v)]
    (hK : HasCardinalLT (Arrow K) κ) [HasLimitsOfShape K A] :
    PreservesColimitsOfShape J (lim : (K ⥤ A) ⥤ A) := by
  have := Functor.isCardinalAccessible_lim (K := K) κ hK
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible (lim : (K ⥤ Type v) ⥤ Type v) κ J
  have := preservesColimitsOfShape_of_isCardinalPresentable G κ J
  have : PreservesColimitsOfShape J
      ((Functor.whiskeringRight K A (Type v)).obj (coyoneda.obj (op G))) :=
    preservesColimitsOfShape_of_evaluation _ _ fun k ↦
      inferInstanceAs (PreservesColimitsOfShape J
        ((evaluation K A).obj k ⋙ coyoneda.obj (op G)))
  have : PreservesColimitsOfShape J ((lim : (K ⥤ A) ⥤ A) ⋙ coyoneda.obj (op G)) :=
    preservesColimitsOfShape_of_natIso (preservesLimitNatIso (coyoneda.obj (op G))).symm
  have := (isDetector_iff_reflectsIsomorphisms_coyoneda_obj G).1 hG.isDetector
  have : ReflectsColimitsOfShape J (coyoneda.obj (op G)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves (lim : (K ⥤ A) ⥤ A) (coyoneda.obj (op G))

end CategoryTheory
