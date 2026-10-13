/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare

/-! # Coefficient factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The shifted coefficient part of scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def scalarCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W Y : Scheme.{u}} (h : Y ⟶ W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((RawModuleScalarComparison.forget Λ W).obj G)))⟦q⟧ :=
  ((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj G)) ≫
    (shiftFunctor _ q).map
      (((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ h G)))

/-- The last two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

/-- The last two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

/-- The shifted coefficient square for scalar forgetting and composite inverse image.
Source: Stacks Project, Tags 03D7 and 03Q8, and the coefficient-factor calculation
in lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-coefficient-square).

Proof: The scalar Kan-extension and sheafification comparisons commute with their
units, so their composite is the inverse-image mate of scalar forgetting.
The unit equation defining upperStarComp therefore identifies scalar forgetting
of its inverse on G with the abelian upperStarComp inverse. Apply singleFunctor;
naturality and composition compatibility of mapDerivedCategoryPlusSingleFunctor
insert the single comparison components and derivedPullbackIso. Shift this
square by q. The derived natural isomorphism induced by pullbackIso commutes
with shifts, as do the derived composition comparison isomorphisms (these come
from the exact functors on complexes). Their composite derivedPullbackIso thus
commutes with shifts. Use this equation and naturality of commShiftIso to
move the shifted single comparisons to the displayed positions. Associativity
gives the displayed equation. This uses neither a free source sheaf nor a
cohomology class, and is valid for all integer shifts, including zero and
negative shifts, identity arrows, and the zero coefficient sheaf. -/
theorem rawModuleScalar_coefficient_square
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G) q A B f
  (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by sorry

end AlgebraicGeometry.Etale
