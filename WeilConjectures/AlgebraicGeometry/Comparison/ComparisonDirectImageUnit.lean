/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonCounit

/-!
# Unit compatibility of the comparison of direct images

For a morphism of schemes `g : X ⟶ Y`, let `c_g : ν_Y^* Rg_* ⟶ Rg_* ν_X^*` be the comparison
of bounded below direct images (`fixedComparisonDirectImageMatePlus`) and
`β_g : g^* ν_Y^* ≅ ν_X^* g^*` the comparison of inverse images
(`fixedComparisonPullbackPlus`). We show that `ν_Y^*` of the étale unit followed by `c_g`
equals the pro-étale unit followed by `Rg_*(β_g)`
(blueprint: `lemma-comparison-direct-images-compatibilities--1`). The counit version
(blueprint: `lemma-comparison-direct-images-compatibilities--2`) is
`fixedComparisonDirectImageMatePlus_transpose`, the general form of
`fixedComparisonDirectImageMatePlus_counit` (which assumes `Λ` finite and `g` qcqs).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Counit compatibility of the comparison of direct images, for an arbitrary morphism `g` and
coefficient ring `Λ`: `g^*(c_g)` followed by the pro-étale counit equals `β_g` followed by
`ν_X^*` of the étale counit, where the direction of `β_g` is
`ν_X^* g^* ⟶ g^* ν_Y^*` (blueprint: `lemma-comparison-direct-images-compatibilities--2`).
This is `fixedComparisonDirectImageMatePlus_counit` without its unused finiteness and
qcqs hypotheses, proved by the same mate calculation. -/
theorem fixedComparisonDirectImageMatePlus_transpose (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixedComparisonPullbackPlus Λ f).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
          K) := by
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f
  let θ := (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
  have hb : fixedComparisonDirectImageMatePlus Λ f =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus θ.hom).natTrans := by
    unfold fixedComparisonDirectImageMatePlus
    rw [ComparisonCore.underived_comparison_mate,
      Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv]
  rw [hb, mateEquiv_counit]
  have hθ : (fixedComparisonPullbackPlus Λ f).hom = θ.inv := by
    have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
        (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
      apply NatTrans.ext
      funext X
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.mapDerivedCategoryNatIso_symm]
      have h : DerivedCategory.Plus.ι.mapIso
          ((Functor.mapDerivedCategoryPlusNatIso σ).app X) =
          (Functor.mapDerivedCategoryNatIso σ).app X.obj :=
        Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ X)
      exact (congrArg Iso.inv h).symm
    simp only [fixedComparisonPullbackPlus, θ, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, Category.assoc, σ]
  rw [hθ]
  exact θ.inv_hom_id_app_assoc _ _

/-- Unit compatibility of the comparison of direct images: for `L ∈ D⁺(Y_ét, Λ)`, the composite
`ν_Y^* L ⟶ ν_Y^* Rg_* g^* L ⟶ Rg_* ν_X^* g^* L` of `ν_Y^*` of the étale unit with `c_g` equals
the pro-étale unit `ν_Y^* L ⟶ Rg_* g^* ν_Y^* L` followed by `Rg_*(β_g)`
(blueprint: `lemma-comparison-direct-images-compatibilities--1`). -/
theorem fixedComparisonDirectImageMatePlus_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).unit.app L) ≫
      (fixedComparisonDirectImageMatePlus Λ g).app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L) =
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.map
          ((fixedComparisonPullbackPlus Λ g).inv.app L) := by
  let adj := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g
  let adjE := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g
  let β := fixedComparisonPullbackPlus Λ g
  apply (adj.homEquiv _ _).symm.injective
  have hc : (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ g).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) ≫
      adj.counit.app ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) =
      β.inv.app _ ≫ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map
        (adjE.counit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) := by
    rw [← fixedComparisonDirectImageMatePlus_transpose]
    exact (β.inv_hom_id_app_assoc _ _).symm
  simp only [Adjunction.homEquiv_counit, Functor.id_obj]
  erw [Functor.map_comp, Category.assoc, hc]
  rw [Functor.map_comp, Category.assoc, adj.counit_naturality, adj.left_triangle_components_assoc]
  have hβ := β.inv.naturality (adjE.unit.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hβ
  rw [← Category.assoc, hβ, Category.assoc, ← Functor.map_comp]
  erw [adjE.left_triangle_components]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale
