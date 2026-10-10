/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity

/-!
# Associativity of the composition isomorphisms of derived pullbacks

The composition isomorphisms `AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the
pullbacks on the bounded below derived categories satisfy the associativity law of a
pseudofunctor, as do the composition isomorphisms `AlgebraicGeometry.Etale.upperStarComp` of
the underived pullbacks from which they are induced
(`AlgebraicGeometry.Etale.upperStarComp_assoc'`).

## Main results

- `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc`: the associativity law, with all
  three composites of the morphisms named.
- `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc_app`: its component form.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

/-- The associativity law for the composition isomorphisms of the derived pullbacks, with all
three composites of the morphisms named. -/
lemma Etale.upperStarCompDerivedPlus_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g)
    (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh) :
    (upperStarCompDerivedPlus A f gh fgh hfgh').hom ≫
        Functor.whiskerRight (upperStarCompDerivedPlus A g h gh hgh).hom
          ((f)^*[A]).mapDerivedCategoryPlus =
      (upperStarCompDerivedPlus A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft ((h)^*[A]).mapDerivedCategoryPlus
          (upperStarCompDerivedPlus A f g fg hfg).hom := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (((f)^*[A]).mapDerivedCategoryPlus.map (((g)^*[A]).mapDerivedCategoryPlus.map
      (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    ((f)^*[A]).mapDerivedCategoryPlus.map
      (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app (((h)^*[A]).mapHomotopyCategoryPlus.obj K))
      ≫ ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj (((h)^*[A]).mapHomotopyCategoryPlus.obj K)))]
  -- the left-hand side
  have hL₁ := upperStarCompDerivedPlus_hom_app_factorsh A g h gh hgh K
  have hL₂ := ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g h gh hgh).hom).app K)
  have hL₃ := upperStarCompDerivedPlus_hom_app_factorsh A f gh fgh
    hfgh' K
  simp only [Functor.comp_obj, Functor.comp_map] at hL₂
  have hL : (upperStarCompDerivedPlus A f gh fgh hfgh').hom.app
        (DerivedCategory.Plus.Qh.obj K) ≫
      ((f)^*[A]).mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus A g h gh hgh).hom.app (DerivedCategory.Plus.Qh.obj K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlus.map (((g)^*[A]).mapDerivedCategoryPlus.map
        (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlus.map
        (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) =
      ((fgh)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f gh fgh hfgh').hom).app K) ≫
        DerivedCategory.Plus.Qh.map (((f)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g h gh hgh).hom).app K)) := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hL₁]
    erw [Functor.map_comp]
    rw [Category.assoc]
    erw [hL₂]
    erw [reassoc_of% hL₃]
  -- the right-hand side
  have hR₁ := (upperStarCompDerivedPlus A f g fg hfg).hom.naturality
    (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)
  have hR₂ := upperStarCompDerivedPlus_hom_app_factorsh A f g fg hfg
    (((h)^*[A]).mapHomotopyCategoryPlus.obj K)
  have hR₃ := upperStarCompDerivedPlus_hom_app_factorsh A fg h fgh hfgh K
  simp only [Functor.comp_obj, Functor.comp_map] at hR₁
  have hR : (upperStarCompDerivedPlus A fg h fgh hfgh).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      (upperStarCompDerivedPlus A f g fg hfg).hom.app
        (((h)^*[A]).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlus.map (((g)^*[A]).mapDerivedCategoryPlus.map
        (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlus.map
        (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) ≫
      ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) =
      ((fgh)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A fg h fgh hfgh).hom).app K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f g fg hfg).hom).app (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) := by
    erw [← reassoc_of% hR₁]
    rw [hR₂]
    erw [reassoc_of% hR₃]
  simp only [Category.assoc] at hL hR ⊢
  rw [hL, hR]
  congr 1
  have key := congrArg (fun τ ↦ DerivedCategory.Plus.Qh.map
    ((NatTrans.mapHomotopyCategoryPlus τ).app K))
    (Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh)
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app, Functor.map_comp] at key
  exact key

/-- The component form of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc`. -/
@[reassoc]
lemma Etale.upperStarCompDerivedPlus_assoc_app {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g)
    (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
    (upperStarCompDerivedPlus A f gh fgh hfgh').hom.app K ≫
        ((f)^*[A]).mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus A g h gh hgh).hom.app K) =
      (upperStarCompDerivedPlus A fg h fgh hfgh).hom.app K ≫
        (upperStarCompDerivedPlus A f g fg hfg).hom.app
          (((h)^*[A]).mapDerivedCategoryPlus.obj K) :=
  NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc A f g h fg gh fgh hfg hgh hfgh hfgh') K

end AlgebraicGeometry
