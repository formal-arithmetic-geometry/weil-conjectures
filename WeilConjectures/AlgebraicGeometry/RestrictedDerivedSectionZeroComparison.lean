/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.DerivedSectionPullbackZero
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionZeroTransport
import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The zero comparison for restricted derived section pullback

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Derived section pullback is the derived adjunction unit followed by Leray. -/
noncomputable def derivedSectionPullback {X Y : Scheme.{v}} (f : X ⟶ Y) :
    rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y ⟶
      D(upperStar AddCommGrpCat.{v + 1} f) ⋙
        rightDerivedGlobalSections AddCommGrpCat.{v + 1} X :=
  Functor.whiskerRight
      (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y) ≫
    Functor.whiskerLeft D(upperStar AddCommGrpCat.{v + 1} f)
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar AddCommGrpCat.{v + 1} f)
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
        (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
            (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal) ≪≫
          lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
          (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
            terminalIsTerminal).symm)).hom

/-- The comparison of the two restrictions in a pullback triangle, on derived objects. -/
noncomputable def derivedRestrictionIso {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)) ≅
      D(upperStar AddCommGrpCat.{v + 1} a) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')) := by
  let q := rawAffineRestrictedMap a h h' w U
  let r := Limits.pullback.snd U.hom h
  let r' := Limits.pullback.snd U.hom h'
  have hw : r' ≫ a = q ≫ r := by simp [q, r, r', rawAffineRestrictedMap]
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso ((upperStarComp AddCommGrpCat.{v + 1} q r).symm ≪≫
      upperStarComp AddCommGrpCat.{v + 1} r' a (q ≫ r) hw.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Natural pullback on zeroth homology of restricted derived sections. -/
noncomputable def restrictedSectionPullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0 ⟶
      D+(upperStar AddCommGrpCat.{v + 1} a) ⋙
        sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0 :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft DerivedCategory.Plus.ι
          (derivedRestrictionIso a h h' w U).hom)
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h')))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0)

/-- On a single sheaf in degree zero, the constructed derived section pullback is
ordinary section pullback, followed by the restricted coefficient map. -/
theorem restrictedSectionPullback_zero {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ψ : (upperStar AddCommGrpCat.{v + 1} a).obj G ⟶ G') (U : S.Etale) :
    (restrictedSectionPullback a h h' w U).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      (sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
          (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map ψ) =
      (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).hom ≫
        globalSectionsUpperStarMap AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
          ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj G) ≫
        (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}).map
          (rawAffineRestrictedCoefficient a h h' w G G' ψ U) ≫
        (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) G').inv := by
  apply (cancel_mono
    (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) G').hom).mp
  have ht := derivedRestriction_zero_transport a h h' w G G' ψ U
  have hp := derivedSectionPullback_zero
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
    (rawAffineRestrictedMap a h h' w U) G
  dsimp only at ht hp
  dsimp only [restrictedSectionPullback, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app]
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [ht]
  erw [← Category.assoc, ← Category.assoc, hp]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Etale.RawRestrictedComparison
