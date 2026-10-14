/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-! # Target transition under a thickening

Source: Stacks Tags 03SI and 0F07, condition (1).
(blueprint: lem-sbc-target-transition-thickening)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma transition_eq_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {A : D ⥤ E} {B : E ⥤ D}
    {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adjA : A ⊣ B) (adj' : L' ⊣ R') (c : L' ≅ L ⋙ A) (K : D) :
    adj'.unit.app (R.obj K) ≫
        R'.map (c.hom.app (R.obj K) ≫ A.map (adj.counit.app K)) =
      R.map (adjA.unit.app K) ≫
        (conjugateIsoEquiv (adj.comp adjA) adj' c).hom.app (A.obj K) := by
  let γ := (conjugateIsoEquiv (adj.comp adjA) adj' c).hom
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm ((adj'.homEquiv _ _)
      (c.hom.app (R.obj K) ≫ A.map (adj.counit.app K))) =
    (adj'.homEquiv _ _).symm (R.map (adjA.unit.app K) ≫ γ.app (A.obj K))
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm]
  change _ = L'.map (R.map (adjA.unit.app K)) ≫
    (L'.map (γ.app (A.obj K)) ≫ adj'.counit.app (A.obj K))
  have hc := conjugateEquiv_counit (adj.comp adjA) adj' c.hom (A.obj K)
  change L'.map (γ.app (A.obj K)) ≫ adj'.counit.app (A.obj K) =
    c.hom.app (R.obj (B.obj (A.obj K))) ≫ (adj.comp adjA).counit.app (A.obj K) at hc
  have hn := c.hom.naturality (R.map (adjA.unit.app K))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [hc, ← Category.assoc, hn]
  rw [Adjunction.comp_counit_app]
  simp only [Category.assoc, Functor.id_obj]
  have he := adj.counit.naturality (adjA.unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at he
  rw [← A.map_comp_assoc, he]
  simp only [A.map_comp, Category.assoc]
  have ht := adjA.left_triangle_components K
  rw [ht]
  simp only [Functor.id_obj, Category.comp_id]

/-- A target transition above a thickening is an isomorphism.

Source: Stacks Tag 03SI and condition (1) in the proof of Tag 0F07.
(blueprint: lem-sbc-target-transition-thickening)

Proof: a base change of a thickening is a thickening: it is a closed immersion and
surjective on points. Pullback along a therefore gives an equivalence of étale sheaf
categories. The equivalence and its inverse are exact; applying them degreewise
and localizing at quasi-isomorphisms gives inverse equivalences on D+. Hence the
unit of the derived adjunction for a is invertible. Under `Rh'_* ≅ Rh_* Ra_*`, the
transition is `Rh_*` applied to this unit: expand the composite adjunction unit and
cancel the h-unit and h-counit by their triangle identity to recover its defining
mate formula. The remaining factors compare pullback along `a ≫ e` and `e' ≫ i`
using sq.w and compare sheaves placed in degree zero. They are isomorphisms, as
are their direct images. Apply degree-q homology, which preserves isomorphisms.
-/
theorem Etale.baseChangeTargetTransition_isIso_of_thickening
    {X T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X) (q : ℤ)
    (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (a : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (sq : IsPullback a e₁ e₂ i) (wh : a ≫ h₂ = h₁)
    (F : Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeTargetTransition Λ e₂ h₂ q i a e₁ h₁ sq.w wh F) := by
  subst h₁
  have : Surjective i := ⟨hi⟩
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip ‹IsClosedImmersion i›
  have : Surjective a := MorphismProperty.of_isPullback sq.flip ‹Surjective i›
  have : ((a)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
    Etale.isEquivalence_upperStar_of_thickening (ModuleCat.{u + 1} Λ) a a.surjective
  have : (D+((a)^*[ModuleCat.{u + 1} Λ])).Full :=
    Functor.Full.of_comp_faithful_iso
      ((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility
  have : (D+((a)^*[ModuleCat.{u + 1} Λ])).Faithful :=
    Functor.Faithful.of_comp_iso
      ((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility
  have ht (K : DerivedCategory.Plus
      (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso (Etale.lowerStarPlusTransition Λ a h₂ (a ≫ h₂) rfl K) := by
    simp only [Etale.lowerStarPlusTransition, eqToIso_refl, Iso.refl_trans]
    rw [transition_eq_unit
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h₂)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h₂))
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h₂) K]
    infer_instance
  unfold Etale.baseChangeTargetTransition
  apply Functor.map_isIso

end AlgebraicGeometry
