/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import WeilConjectures.CategoryTheory.FilteredColimitPullbackLift
import WeilConjectures.CategoryTheory.FilteredColimitPullbackHomExt
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Pullbacks preserved at every later stage of a filtered category colimit

Source: Stacks Project, Sites, Tag 09YL, pullback paragraph.
-/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A stage pullback preserved by every transition out of that stage is preserved
by the canonical functor to a category whose object and arrow cocones are colimits.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and its Hom calculation. -/
theorem filteredColimit_preservesPullback
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    PreservesLimit (cospan f g) (V.ι.app j).toFunctor := by
  classical
  let U := (V.ι.app j).toFunctor
  let t : PullbackCone f g :=
    PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition)
  have hex := filteredColimit_pullback_exists J F V hobjects harrows j f g hpres
  have hext := filteredColimit_pullback_hom_ext J F V hobjects harrows j f g hpres
  have ht : IsLimit (t.map U) := by
    apply PullbackCone.isLimitAux'
    intro s
    let h := hex s.pt s.fst s.snd s.condition
    let l := h.choose
    have hl := h.choose_spec.1
    have hr := h.choose_spec.2
    refine ⟨l, hl, hr, ?_⟩
    intro m hm₁ hm₂
    exact hext s.pt m l (hm₁.trans hl.symm) (hm₂.trans hr.symm)
  exact preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
    ((PullbackCone.isLimitMapConeEquiv t U).symm ht)

end CategoryTheory
