/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # DerivedPulledGlobalGermFac

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

/-- The source-side derived germ and exchange, precomposed with the global-sections
unit, are the localized underived source-side composite followed by the target units.
Source: Stacks Project, sites-cohomology.tex, Remark 08J6 and Lemma 0736;
cohomology.tex, Tag 01EZ.
(blueprint: lem-weil-pbc-derived-pulled-global-germ-fac)

Proof: Expand `derivedPulledGlobalGerm`. The Leray unit compatibility moves the
Γ_X unit across the inverse Leray comparison, giving the localized inverse terminal
section isomorphism followed by the composite Γ_Y and f_* units. Naturality moves the
f_* unit through the derived pulled germ. The defining compatibility of the right-derived
natural transformation with its units replaces the Γ_Y unit followed by the derived
pulled germ by its termwise map. The exact-functor comparison and composition comparison
replace the remaining derived unit by the two stalk/pullback factorization inverses.
Use `derivedBaseChangeMapPlus_fac_app` to replace the pullback of the f_* unit followed
by exchange by the termwise exchange, the f'_* unit and the g'^* comparison inverse.
Naturality of the stalk factorization collects the three target comparisons into c.
Functoriality of the homotopy quotient and localization combines the preceding maps
into the localization of `NatTrans.mapHomotopyCategoryPlus a`. -/
theorem derivedPulledGlobalGerm_fac
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
    let a : H ⟶ G' ⋙ F' ⋙ S :=
      (lowerStarCompGlobalSectionsIso B f).inv ≫
        Functor.whiskerLeft F (pulledGlobalGerm g t) ≫
        (Functor.associator F G S).inv ≫
        Functor.whiskerRight (baseChangeMap B sq) S ≫
        (Functor.associator G' F' S).hom
    let c := S.mapDerivedCategoryPlusFactorsh.inv.app
        (F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map
        (F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map (F'.rightDerivedFunctorPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app M))
    H.rightDerivedFunctorPlusUnit.app M ≫
        (derivedPulledGlobalGerm f g t).app (DerivedCategory.Plus.Qh.obj M) ≫
        S.mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus B sq).app (DerivedCategory.Plus.Qh.obj M)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus a).app M) ≫ c := by sorry

end AlgebraicGeometry.Etale
