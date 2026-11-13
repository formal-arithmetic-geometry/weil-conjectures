/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Scalar forgetting and composition on sheaves

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

-- The canonical adjunction mate satisfies its defining unit equation.
private lemma scalar_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((moduleAbelianForget Λ S).obj G) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.pullback Λ f G) =
      (moduleAbelianForget Λ S).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app G) = _
  exact Equiv.apply_symm_apply _ _

/-- Scalar forgetting commutes with inverse-image composition before deriving.
-/
theorem rawModuleScalar_sheaf_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    RawModuleScalarComparison.pullback Λ h' L ≫
        (moduleAbelianForget Λ Y').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) =
      (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
          ((moduleAbelianForget Λ S).obj L) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          (RawModuleScalarComparison.pullback Λ h L) ≫
        RawModuleScalarComparison.pullback Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)  := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h').homEquiv _ _ |>.injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, scalar_unit Λ h' L]
  change (moduleAbelianForget Λ S).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h').unit.app L) ≫
      (moduleAbelianForget Λ S).map
        ((lowerStar (ModuleCat.{u + 1} Λ) h').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L)) = _
  rw [← Functor.map_comp,
    upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) a h L h' w.symm]
  rw [Functor.map_comp]
  rw [reassoc_of% (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} a h
    ((moduleAbelianForget Λ S).obj L) h' w.symm)]
  rw [reassoc_of% ((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} a).map
      (RawModuleScalarComparison.pullback Λ h L))).symm]
  erw [((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    (RawModuleScalarComparison.pullback Λ a
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L))).symm]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn := congrArg (lowerStar AddCommGrpCat.{u + 1} h).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.naturality
      (RawModuleScalarComparison.pullback Λ h L))
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn.symm]
  rw [← (lowerStar AddCommGrpCat.{u + 1} h).map_comp_assoc
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app
      ((moduleAbelianForget Λ Y).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))
    ((lowerStar AddCommGrpCat.{u + 1} a).map
      (RawModuleScalarComparison.pullback Λ a
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))]
  rw [scalar_unit Λ a ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)]
  rw [reassoc_of% (scalar_unit Λ h L)]
  rfl

end AlgebraicGeometry.Etale
