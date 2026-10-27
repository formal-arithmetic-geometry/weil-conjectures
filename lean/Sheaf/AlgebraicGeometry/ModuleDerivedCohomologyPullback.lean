module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical module-valued derived cohomology pullback

Source: Stacks Project, Tags 01EZ, 01F8, 01F9 and 01FA
(blueprint: def-weil-pbc-cohomology-pullback).
The recorded abelian sheaf cohomology map is publicly imported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Canonical composition comparison for module-valued derived global sections.
Source: Stacks Tag 01EZ (blueprint: def-weil-pbc-cohomology-pullback). -/
@[irreducible]
def moduleLerayPlus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus ⋙
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅
        (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus :=
  @Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (lowerStar (ModuleCat.{u + 1} A) f)
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _ _ _
    (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) f)

/-- Canonical pullback, constructed by deriving the ordinary section pullback using
right-derived descent. On injective resolutions this is the ordinary section map followed
by a resolution comparison. Source: Stacks Tags 01F8--01FA
(blueprint: def-weil-pbc-cohomology-pullback). -/
@[irreducible]
def moduleDerivedCohomologyPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj K ⟶
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K) :=
  (Functor.rightDerivedDesc _
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus)
      (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus
            ((Functor.leftUnitor _).inv ≫
              Functor.whiskerRight (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit
                (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f)
                (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) f).hom))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
              Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)))).inv
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryPlus
          (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlusFactorsh.inv
          (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom )).app K

/-- Canonical abelian pullback, constructed by deriving the ordinary section pullback using
right-derived descent. On injective resolutions this is the ordinary section map followed
by a resolution comparison. Source: Stacks Tags 01F8--01FA
(blueprint: def-weil-pbc-cohomology-pullback). -/
@[irreducible]
def abelianDerivedCohomologyPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1}))) :
    (Sheaf.Γ X.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlus.obj K ⟶
      (Sheaf.Γ Y.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlus.obj
        ((upperStar (AddCommGrpCat.{u + 1}) f).mapDerivedCategoryPlus.obj K) :=
  (Functor.rightDerivedDesc _
      (Sheaf.Γ X.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
      ((upperStar (AddCommGrpCat.{u + 1}) f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ Y.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlus)
      (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus
            ((Functor.leftUnitor _).inv ≫
              Functor.whiskerRight (upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f).unit
                (Sheaf.Γ X.smallEtaleTopology (AddCommGrpCat.{u + 1})) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (upperStar (AddCommGrpCat.{u + 1}) f)
                (lowerStarCompGlobalSectionsIso (AddCommGrpCat.{u + 1}) f).hom))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (upperStar (AddCommGrpCat.{u + 1}) f ⋙
              Sheaf.Γ Y.smallEtaleTopology (AddCommGrpCat.{u + 1})))).inv
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar (AddCommGrpCat.{u + 1}) f).mapHomotopyCategoryPlus
          (Sheaf.Γ Y.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlusUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStar (AddCommGrpCat.{u + 1}) f).mapDerivedCategoryPlusFactorsh.inv
          (Sheaf.Γ Y.smallEtaleTopology (AddCommGrpCat.{u + 1})).rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom )).app K

end AlgebraicGeometry.Etale
