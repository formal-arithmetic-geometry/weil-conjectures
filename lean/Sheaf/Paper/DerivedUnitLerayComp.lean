/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! # Coherence of the derived unit and Leray comparison -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
/-- The derived unit--Leray composites respect inverse-image composition.
Source: Stacks Project, Tags 015M and 03CB.
(blueprint: lem-weil-pbc-derived-unit-leray-comp).

Proof: Write U_f and U_g for the exact functors induced on derived categories, R_f and R_g for the
derived direct images, C:U_(g≫f)≅U_f followed by U_g for mapDerivedCategoryNatIso(upperStarComp)
followed by mapDerivedCategoryCompIso, and D:R_g followed by R_f≅R_(g≫f) for its conjugate. The
derived adjunction unit equation states eta_(g≫f),K followed by R_(g≫f)(C_K) equals eta_f,K
followed by R_f(eta_g,U_f(K)) followed by D_(U_g(U_f(K))). It is the unit-conjugation equation
for the adjunctions; the conjugate agrees with the canonical derived direct-image composition by
the right-derived comparison characterization.

The underived direct-image and terminal-section comparisons associate: evaluating an iterated
base change of the terminal object is the same as evaluating its composite base change, because
both isomorphisms commute with its projections. Deriving that equation yields RGamma_X(D_M)
followed by lambda_(g≫f),M equal to lambda_f,R_g(M) followed by lambda_g,M. Indeed both sides
precomposed with the composite right-derived unit are the localization of that underived
comparison. Direct image preserves K-injectives, so the composite right-derived functor has the
universal property, which makes these transformations equal.

Use naturality of lambda_(g≫f) at C_K to move RGamma_Z(C_K) across lambda_(g≫f). Substitute the
unit equation from step 1 and then the Leray composition equation from step 2, with
M=U_g(U_f(K)). The resulting composite contains RGamma_X(R_f(eta_g,U_f(K))) followed by
lambda_f,R_g(U_g(U_f(K))). Naturality of lambda_f at eta_g,U_f(K) replaces these by
lambda_f,U_f(K) followed by RGamma_Y(eta_g,U_f(K)). After reassociating, the result is exactly
the product of the unit-Leray composites for f at K and for g at U_f(K). -/
theorem derivedUnitLeray_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (g ≫ f)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} (g ≫ f)).hom.app
      ((upperStar AddCommGrpCat.{u + 1} (g ≫ f)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Z).map
      ((Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} g f) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar AddCommGrpCat.{u + 1} f)
          (upperStar AddCommGrpCat.{u + 1} g)).hom.app K) =
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} f).hom.app
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj K)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
