/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphUnitTensor
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso

/-! # The graph comparison and the etale projection formula over arbitrary bases

The graph comparison is the upstream `compactificationEtaleComparison`, constructed
from clopen graph transfer and inverse proper exchange. The helpers merely insert the
canonical exact/left-derived comparison into the existing projection maps.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The inverse tensor comparison for exact inverse image, transported from derived pullback:
`supportExactPullbackTensorIso` at the coefficients `ModuleCat A`. -/
noncomputable abbrev sfEtaleExactPullbackTensorIso
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W)
    (B K : DerivedCategoryModule A W) :
    D((e)^*[ModuleCat.{u + 1} A]).obj
        (((derivedTensor (ModuleCat.{u + 1} A) W).obj B).obj K) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        (D((e)^*[ModuleCat.{u + 1} A]).obj B)).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K) :=
  supportExactPullbackTensorIso (ModuleCat.{u + 1} A) e B K

/-- The unit-adjunct tensor action for exact etale sum extension: the inverse Hom transpose of
the sum/evaluation unit tensored with the identity, followed by the inverse tensor comparison. -/
noncomputable def sfEtaleSumExactTensorMap
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W) [Etale e]
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) W).obj
        (D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).obj K :=
  ((derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).homEquiv _ _).symm
    (((derivedTensor (ModuleCat.{u + 1} A) V).map
        ((derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).unit.app M)).app _ ≫
      (sfEtaleExactPullbackTensorIso A e
        (D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) K).inv)

/-- The proper-counit/open-tensor projection isomorphism, with target transported to the exact
inverse-image model along the canonical comparison of `Le^*` with `D(e^*)`. -/
noncomputable def sfEtaleExactProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} {e : V ⟶ W} (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    ((derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) :=
  haveI := (sfEtaleAmbientAdjointProjection A c).2 M K
  asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso
      (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).app K))

private theorem graphUnit_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (M : DerivedCategoryModule A V) :
    (derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).unit.app M ≫
        D((e)^*[ModuleCat.{u + 1} A]).map
          ((compactificationEtaleComparison A e c).app M) =
      (compactificationEtaleUnit A e c).app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app _ := by
  have h := unit_map_compactificationEtaleComparison A e c M
  simp only [derivedEtaleLowerShriekAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom] at h
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) e).hom.naturality ((compactificationEtaleComparison A e c).app M)
  dsimp at hn
  rw [← h]
  simp only [Category.assoc]
  erw [hn]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem exactTensor_inv_naturality
    (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (e : V ⟶ W)
    {B B' : DerivedCategoryModule A W} (f : B ⟶ B')
    (K : DerivedCategoryModule A W) :
    (sfEtaleExactPullbackTensorIso A e B K).inv ≫
        D((e)^*[ModuleCat.{u + 1} A]).map
          (((derivedTensor (ModuleCat.{u + 1} A) W).map f).app K) =
      ((derivedTensor (ModuleCat.{u + 1} A) V).map
        (D((e)^*[ModuleCat.{u + 1} A]).map f)).app _ ≫
          (sfEtaleExactPullbackTensorIso A e B' K).inv := by
  let H := D((e)^*[ModuleCat.{u + 1} A])
  let J := L((e)^*[ModuleCat.{u + 1} A])
  let τ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  let T := derivedTensor (ModuleCat.{u + 1} A) W
  let T' := derivedTensor (ModuleCat.{u + 1} A) V
  let δ := (Functor.postcompose₂.mapIso τ.symm).app T ≪≫
    leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A V)).mapIso τ).app J).app T' ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A V)).obj H).mapIso τ).app T'
  exact (NatTrans.congr_app (δ.inv.naturality f) K).symm

/-- The graph comparison `compactificationEtaleComparison` is a natural isomorphism, and it
intertwines the proper-counit/open-tensor projection with the sum/evaluation unit-adjunct tensor
action. -/
theorem sfEtaleGraphProjectionArbitraryBase
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e] (c : Compactification e) :
    IsIso (compactificationEtaleComparison A e c) ∧
      ∀ (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W),
        (compactificationEtaleComparison A e c).app
              (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
                (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ≫
            (sfEtaleExactProjectionIso A c M K).inv =
          sfEtaleSumExactTensorMap A e M K ≫
            ((derivedTensor (ModuleCat.{u + 1} A) W).map
              ((compactificationEtaleComparison A e c).app M)).app K := by
  refine ⟨isIso_compactificationEtaleComparison A e c, ?_⟩
  intro M K
  apply (cancel_mono (sfEtaleExactProjectionIso A c M K).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ((derivedEtaleLowerShriekMapAdjunction
    (ModuleCat.{u + 1} A) e).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [sfEtaleSumExactTensorMap, Equiv.apply_symm_apply,
    Functor.map_comp, Category.assoc]
  rw [Adjunction.homEquiv_unit, graphUnit_exact, sfEtaleGraphUnitTensor]
  rw [reassoc_of% (exactTensor_inv_naturality A e
    ((compactificationEtaleComparison A e c).app M) K)]
  have hc := congrArg
    (fun f ↦ ((derivedTensor (ModuleCat.{u + 1} A) V).map f).app
      (D((e)^*[ModuleCat.{u + 1} A]).obj K)) (graphUnit_exact A e c M)
  simp only [Functor.map_comp, NatTrans.comp_app] at hc
  rw [reassoc_of% hc]
  simp only [sfEtaleExactProjectionIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
