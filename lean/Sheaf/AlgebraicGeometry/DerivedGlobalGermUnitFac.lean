/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction

import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit

/-! # DerivedGlobalGermUnitFac

Source: Stacks Project, Tags 095T, 01F8 and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- The target-side derived unit and germ, precomposed with the global-sections unit,
are the localized section-unit-and-germ composite followed by the target units.
Source: Stacks Project, cohomology.tex, Tags 01EZ and 01F8;
sites-cohomology.tex, Remark 08J6.
(blueprint: lem-weil-pbc-derived-global-germ-unit-fac)

Proof: Use `derivedCohomologyPullback_eq_derivedUnit` to replace Γ of the derived
adjunction unit followed by Leray by the derived pullback of sections. Its defining
right-derived descent formula, precomposed with Γ_X's unit, is the localized section
unit, followed by Γ_X' on the homotopy category and the inverse g'^* factorization.
Move that inverse across the target germ by naturality. Expand the target derived
germ: the Leray unit compatibility and the right-derived natural-transformation unit
compatibility turn Γ_X' followed by its germ into the localized inverse terminal
section identification and underived germ. The exact stalk comparison contributes the
inverse stalk factorization followed by the stalk image of the f'_* unit.
Combine localized maps using functoriality; the underived map is precisely b and the
remaining three comparisons, in their order, are c. -/
theorem derivedGlobalGerm_unit_fac
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : CommSq g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (M : HomotopyCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    let B := AddCommGrpCat.{u + 1}
    let F := lowerStar B f
    let F' := lowerStar B f'
    let G := upperStar B g
    let G' := upperStar B g'
    let R := lowerStar B g'
    let H := Sheaf.Γ X.smallEtaleTopology B
    let S := (pointSmallEtale t).sheafFiber
    let b : H ⟶ G' ⋙ F' ⋙ S :=
      (Functor.leftUnitor H).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction B g').unit H ≫
        (Functor.associator G' R H).hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B g').hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B f').inv ≫
        Functor.whiskerLeft G' (Functor.whiskerLeft F' (globalGerm t))
    let c := S.mapDerivedCategoryPlusFactorsh.inv.app
        (F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map
        (F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map (F'.rightDerivedFunctorPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app M))
    H.rightDerivedFunctorPlusUnit.app M ≫
        (H.rightDerivedFunctorPlus.map
          ((upperStarLowerStarAdjunction B g').derivedPlus.unit.app
            (DerivedCategory.Plus.Qh.obj M)) ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            R H _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction B g'))
            (lowerStarCompGlobalSectionsIso B g')).hom.app
              (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M))) ≫
        (derivedGlobalGerm f' t).app
          (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus b).app M) ≫ c := by sorry

end AlgebraicGeometry.Etale
