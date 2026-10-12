/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Unit--Leray computation on K-injective complexes

Source: Stacks Project, Tags 08BJ, 070I, 01F8, 01F9, 01FA and 08J6.
(blueprint: lem-weil-pbc-kinjective-unit-leray).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The unit--Leray map on K-injective complexes is represented by the sectionwise map.
Source: Stacks Project, Tags 08BJ and 070I; cohomology.tex, Tags 01F8--01FA;
sites-cohomology.tex, Tag 08J6.
(blueprint: lem-weil-pbc-kinjective-unit-leray).

Proof: Adjoint j to a map I → f_*J. Since inverse image is exact, direct image
preserves K-injectives (Tag 08BJ). The derived units on I, J and f_*J are therefore
invertible. Expand the derived adjunction unit using its defining unit compatibility.
Move the factorization isomorphism for exact inverse image through the Leray
isomorphism by naturality. The composite right-derived unit compatibility for
f_* followed by Γ identifies the remaining factors with Γ of the underived
adjunction unit followed by the sectionwise identification Γ_X f_* ≅ Γ_Y.
Naturality of the Γ_Y unit with respect to j gives the last factor Γ_Y(j).
In degree i the resulting chain map is globalSectionsUpperStarMap applied to I.X i
followed by Γ_Y(j.f i), hence it is w by extensionality. Localizing gives the
asserted equality, with the inverse units expressed as rightDerivedFunctorObjQIso.
No resolution augmentation or homology functor is used in this calculation. -/
theorem etaleKInjective_unit_leray
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (I.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i)) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).rightDerivedFunctorObjQIso
        I).hom ≫ DerivedCategory.Q.map w ≫
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).rightDerivedFunctorObjQIso
        J).inv =
      (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
            (DerivedCategory.Q.obj I)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{uNatural + 1} f).hom.app
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
              (DerivedCategory.Q.obj I)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.map j) := by sorry

end AlgebraicGeometry.Etale
