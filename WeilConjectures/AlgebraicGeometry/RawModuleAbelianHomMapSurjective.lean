/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.CategoryTheory.Abelian.DerivedHomComparisonSurjective
import WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceHomBijective
import WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceAcyclic

/-! # Surjective raw scalar comparison

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
/-- Surjective of the raw scalar comparison on underlying groups. -/
theorem rawModuleAbelianHomMap_surjective
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    Function.Surjective (rawModuleAbelianHomMap Λ k G q U A).hom := by
  let V := moduleAbelianForget Λ A.left
  let F := (upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G
  let L := (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)
  let B := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).obj
    (RawModuleScalarComparison.freeAbelian S U)
  let a : B ⟶ V.obj L :=
    (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      RawModuleScalarComparison.pullback Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
  have hs := derivedHomComparison_surjective.{u + 1, u + 1, u + 1, u + 2, u + 2}
    V L B a
    (fun N ↦ (rawModuleFreeSourceHom_bijective Λ (A.hom ≫ k) U N).surjective)
    (fun I _ ↦ rawModuleFreeSource_acyclic Λ (A.hom ≫ k) U I) F q
  let e := inv (RawModuleScalarComparison.pullback Λ A.hom G)
  let d := (shiftFunctor _ (q : ℤ)).map
    ((DerivedCategory.Plus.singleFunctor _ 0).map e)
  have : IsIso d := by dsimp only [d, e]; infer_instance
  let c := (DerivedCategory.Plus.singleFunctor _ 0).map a ≫
    (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L
  let b := (V.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((V.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map e)
  have hb : Function.Surjective
      (((Preadditive.leftComp _ c).comp (Preadditive.rightComp _ b)).comp
        V.mapDerivedCategoryPlus.mapAddHom) := by
    intro y
    obtain ⟨x, hx⟩ := hs (y ≫ inv d)
    refine ⟨x, ?_⟩
    change c ≫ (V.mapDerivedCategoryPlus.map x ≫ b) = y
    have hx' := congrArg (fun z ↦ z ≫ d) hx
    simpa only [c, b, d, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Functor.map_comp] using hx'
  exact hb

end AlgebraicGeometry.Etale
