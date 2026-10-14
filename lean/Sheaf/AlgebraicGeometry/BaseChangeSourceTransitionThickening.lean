/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic

/-! # Source transition under a thickening

Source: Stacks Tags 03SI and 0F07, condition (1).
(blueprint: lem-sbc-source-transition-thickening)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem thickening_unit_isIso
    {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂) [IsClosedImmersion i]
    (hi : Function.Surjective i.base)
    (K : DerivedCategory.Plus (Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) i).unit.app K) := by
  -- Topological invariance makes inverse image fully faithful and preserves injectives.
  have : ((i)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
    Etale.isEquivalence_upperStar_of_thickening (ModuleCat.{u + 1} Λ) i hi
  unfold Etale.derivedUpperStarLowerStarAdjunctionPlus
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  apply Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
  · intro I _
    infer_instance
  · intro I _
    exact ((i)_*[ModuleCat.{u + 1} Λ]).rightAcyclic_of_injective _

set_option backward.isDefEq.respectTransparency false in
private theorem transition_isIso_of_unit
    {S T₁ T₂ : Scheme.{u}} (g : T₂ ⟶ S) (i : T₁ ⟶ T₂)
    (K : DerivedCategory.Plus (Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) i).unit.app K)] :
    IsIso (Etale.lowerStarPlusTransition Λ i g (i ≫ g) rfl K) := by
  have : ((i)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i)
  -- Use the canonical composition comparison, whose unit law is already proved.
  let c := Functor.rightDerivedFunctorPlusCompIso'
    ((i)_*[ModuleCat.{u + 1} Λ]) ((g)_*[ModuleCat.{u + 1} Λ])
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) i g)
  have hc := Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus
    (ModuleCat.{u + 1} Λ) i g (i ≫ g) rfl
    (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K)
  simp only [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus] at hc
  have hn := c.hom.naturality
    (D+((i)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) g).counit.app K))
  have hu := (Etale.derivedUpperStarLowerStarAdjunctionPlus
    (ModuleCat.{u + 1} Λ) i).unit.naturality
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) g).counit.app K)
  have he : Etale.lowerStarPlusTransition Λ i g (i ≫ g) rfl K =
      R+((g)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) i).unit.app K) ≫
        c.hom.app (D+((i)^*[ModuleCat.{u + 1} Λ]).obj K) := by
    unfold Etale.lowerStarPlusTransition
    simp only [eqToIso_refl, Iso.refl_trans, Functor.map_comp]
    change (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) (i ≫ g)).unit.app
        (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((i ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i g).hom.app _) ≫ _ = _
    dsimp only [c, Etale.derivedUpperStarLowerStarAdjunctionPlus] at hn hu ⊢
    rw [reassoc_of% hc]
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn hu
    -- Move the counit past the composition comparison and the unit for i.
    rw [← hn, ← Functor.map_comp_assoc, ← hu]
    simp only [Functor.map_comp, Category.assoc]
    -- The unit and counit for g cancel, leaving Rg applied to the unit for i.
    rw [Adjunction.right_triangle_components_assoc]
  rw [he]
  infer_instance

/-- A source transition along a thickening is an isomorphism.

Source: Stacks Tag 03SI and condition (1) in the proof of Tag 0F07.
(blueprint: lem-sbc-source-transition-thickening)

Proof: pullback along the closed immersion surjective on points is an equivalence of
étale sheaf categories. An additive equivalence and its inverse are exact, so applying
both degreewise and localizing at quasi-isomorphisms gives inverse equivalences on D+.
Thus the unit of the derived adjunction for i is invertible. Under the canonical
identification `R(i ≫ g)_* ≅ Rg_* Ri_*`, the transition is `Rg_*` applied to this unit:
expand the composite adjunction unit and cancel the g-unit and g-counit using their
triangle identity. This agrees with the defining mate formula for the transition.
Pull back along p and apply degree-q homology. The comparison between the pullback
of a degree-zero complex and its pulled-back sheaf in degree zero is an isomorphism,
so every factor of the source transition is invertible.
-/
theorem Etale.baseChangeSourceTransition_isIso_of_thickening
    {X S T₁ T₂ : Scheme.{u}} (p : X ⟶ S) (g : T₂ ⟶ S) (q : ℤ)
    (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (F : Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeSourceTransition Λ p g q i F) := by
  have := thickening_unit_isIso Λ i hi ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have := transition_isIso_of_unit Λ g i ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  unfold Etale.baseChangeSourceTransition
  infer_instance

end AlgebraicGeometry
