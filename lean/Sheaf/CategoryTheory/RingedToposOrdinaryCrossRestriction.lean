/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Ordinary cross-restriction of subterminal direct images

Source: Stacks Project, Cohomology, Tag 08DG, the sectionwise slice calculation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r m
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
/-- The canonical map from a direct image to the overlap direct image is invertible
on the other subterminal slice.
Source: Stacks Project, Cohomology, Tag 08DG (lemma-glue), extended to slice sites.
(blueprint: lem-sp-ringed-topos-ordinary-cross-restriction).

Proof: Evaluate on X → U. For any pullback presentation W of U × V, the
Hom-equivalence formula for the
W-adjunction expresses the component as two presheaf restriction maps. The first
comes from applying V-star to the W-adjunction counit W × X → X. Its underlying
map V × (W × X) → V × X is invertible: an inverse inserts the W-coordinate formed
from X → U and the displayed V-coordinate. The two inverse equations follow from
subterminality of U and V. The second restriction comes from the V-adjunction unit
on the object W × X → V. Since V is subterminal, Over.forget V is full, so its
adjunction unit is invertible. Both presheaf maps are consequently bijective.
The module and presheaf forgetful functors reflect isomorphisms, giving the result.
There is no covering, boundedness, sheafification, or derived-category hypothesis;
empty and equal subterminals are included.
-/
theorem ringedTopos_ordinaryCross_restriction
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]
    [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
    (U V W : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    (tU : W ⟶ U) (tV : W ⟶ V)
    (hW : IsPullback tU tV (terminal.from U) (terminal.from V))
    (M : SheafOfModules.{m} (R.over V)) :
    IsIso ((SheafOfModules.overFunctor.{m} R U).map
      ((SheafOfModules.overPushforwardOverAdj (R := R) W).homEquiv _ _
        ((SheafOfModules.overFunctorMap R tV).inv.app
              ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) V)).obj M) ≫
          (SheafOfModules.overMap R tV).map
            ((SheafOfModules.overPushforwardOverAdj (R := R) V).counit.app M)))) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget (R.over U))).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf (R.over U).obj)).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rw [Adjunction.homEquiv_unit]
  change Function.Bijective (fun x =>
    M.val.presheaf.map
      ((Over.forgetAdjStar V).unit.app
        ((Over.map tV).obj ((Over.star W).obj X.unop.left))).op
      (M.val.presheaf.map
        ((Over.star V).map ((Over.forgetAdjStar W).counit.app X.unop.left)).op x))
  have : (Over.forget V).Full := by
    constructor
    intro A B f
    refine ⟨Over.homMk f ?_, rfl⟩
    apply (cancel_mono (terminal.from V)).mp
    simp
  have : IsIso (Over.forgetAdjStar V).unit := inferInstance
  have hb : IsIso ((Over.star V).map
      ((Over.forgetAdjStar W).counit.app X.unop.left)) := by
    apply (isIso_iff_of_reflects_iso _ (Over.forget V)).mp
    simp only [Over.forget_map, Over.star_map_left, Over.forgetAdjStar_counit_app]
    let h : V ⨯ X.unop.left ⟶ W := hW.lift
      (prod.snd ≫ X.unop.hom) prod.fst (terminal.hom_ext _ _)
    let l : V ⨯ X.unop.left ⟶ V ⨯ (W ⨯ X.unop.left) :=
      prod.lift prod.fst (prod.lift h prod.snd)
    let e : V ⨯ (W ⨯ X.unop.left) ≅ V ⨯ X.unop.left :=
      { hom := prod.map (𝟙 V) prod.snd
        inv := l
        hom_inv_id := by
          apply prod.hom_ext
          · simp [l]
          · apply prod.hom_ext
            · apply hW.hom_ext
              · apply (cancel_mono (terminal.from U)).mp
                exact terminal.hom_ext _ _
              · apply (cancel_mono (terminal.from V)).mp
                exact terminal.hom_ext _ _
            · simp [l]
        inv_hom_id := by
          apply prod.hom_ext <;> simp [l] }
    exact e.isIso_hom
  exact Function.Bijective.comp (ConcreteCategory.bijective_of_isIso _)
    (ConcreteCategory.bijective_of_isIso _)
end CategoryTheory
