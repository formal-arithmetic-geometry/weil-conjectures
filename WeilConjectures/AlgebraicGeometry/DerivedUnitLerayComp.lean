/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.DerivedLerayComp

/-! # Coherence of the derived unit and Leray comparison -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

private theorem derivedUnit_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K ≫
      (lowerStar A (g ≫ f)).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar A f)
            (upperStar A g)).symm).hom.app K) =
    (mapDerivedUpperStarLowerStarAdjunction A f).unit.app K ≫
      (lowerStar A f).rightDerivedFunctor.map
        ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
          ((upperStar A f).mapDerivedCategory.obj K)) ≫
      (rightDerivedLowerStarComp A g f).hom.app
        ((upperStar A g).mapDerivedCategory.obj
          ((upperStar A f).mapDerivedCategory.obj K)) := by
  simpa only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj] using
    (unit_conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction A f).comp
        (mapDerivedUpperStarLowerStarAdjunction A g))
      (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f))
      (Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar A f)
          (upperStar A g)).symm).hom K).symm

/-- The derived unit--Leray composites respect inverse-image composition
(Stacks, Tags 015M and 03CB). -/
theorem derivedUnitLeray_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A (g ≫ f)).hom.app
      ((upperStar A (g ≫ f)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections A Z).map
      ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar A f)
          (upperStar A g)).symm).hom.app K) =
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app
      ((upperStar A f).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections A Y).map
      ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
        ((upperStar A f).mapDerivedCategory.obj K)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A g).hom.app
      ((upperStar A g).mapDerivedCategory.obj
        ((upperStar A f).mapDerivedCategory.obj K)) := by
  let C := Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar A f)
      (upperStar A g)).symm
  let U := (upperStar A f).mapDerivedCategory
  let V := (upperStar A g).mapDerivedCategory
  let R := (lowerStar A f).rightDerivedFunctor
  let G := rightDerivedGlobalSections A X
  let H := rightDerivedGlobalSections A Y
  let eta := (mapDerivedUpperStarLowerStarAdjunction A f).unit.app K
  let theta := (mapDerivedUpperStarLowerStarAdjunction A g).unit.app
    (U.obj K)
  let lambda := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    A f).hom
  let mu := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    A (g ≫ f)).hom
  have hn := mu.naturality (C.hom.app K)
  have hu := congrArg G.map (derivedUnit_comp f g K)
  have hl := derivedLeray_comp f g (V.obj (U.obj K))
  have ht := lambda.naturality theta
  dsimp only [Functor.comp_map] at hn ht
  change G.map _ ≫ mu.app _ ≫ _ =
    G.map eta ≫ lambda.app (U.obj K) ≫ H.map theta ≫ _
  rw [← hn, ← G.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [hl]
  change G.map eta ≫ G.map (R.map theta) ≫ lambda.app _ ≫ _ = _
  erw [reassoc_of% ht]

end AlgebraicGeometry.Etale
