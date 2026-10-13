/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Source factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-source-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

namespace RawModuleScalarComparison

/-- Derive the fixed scalar inverse-image comparison, using composition comparisons.
Source: Stacks Project, Tag 03D7, and exact derived functor comparisons.
No data are chosen from an existence statement.
(blueprint: lem-sbc-raw-scalar-source-square). -/
noncomputable def derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)

end RawModuleScalarComparison

/-- The source part of the scalar comparison, as a fixed derived morphism.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-source-square). -/
noncomputable def scalarSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : E ⟶ (RawModuleScalarComparison.forget Λ S).obj L) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj E) ⟶
      (RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStar AddCommGrpCat.{u + 1} h).map t ≫
        RawModuleScalarComparison.pullback Λ h L) ≫
    ((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)

/-- The first two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-source-square). -/
noncomputable def moduleSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h').obj L) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)

/-- The first two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-raw-scalar-source-square). -/
noncomputable def abelianSourceFactor
    {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h').obj E) ⟶
      (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} h).obj E)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app E) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar AddCommGrpCat.{u + 1} h).obj E)

/-- The source square for scalar forgetting and composite inverse image.
Source: Stacks Project, Tags 03D7 and 03Q8, inverse-image composition, and the
source-factor calculation in lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-source-square).

Proof: The inverse of the scalar Kan-extension comparison commutes with the
Kan-extension unit, and the sheafification comparison commutes with the
sheafification unit. Hence pullbackIso is the mate of the scalar-forgetting
comparison on direct images. The composition unit equation for upperStarComp
then identifies the two ways of forgetting a composite inverse image.
Apply this equation to L; naturality of upperStarComp applied to t moves t
across the source comparison. Apply singleFunctor to the resulting sheaf
square. Naturality of mapDerivedCategoryPlusSingleFunctor and its compatibility
with the derived composition comparison identify the single factors with the
components of derivedPullbackIso. Cancel the single comparison isomorphisms.
This gives the displayed square. It holds for arbitrary E,L,t, including zero
objects and zero maps, and also for identity scheme arrows. No coefficient
sheaf, degree, cohomology class, or invertibility of t is used. -/
theorem rawModuleScalar_source_square
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : E ⟶ (RawModuleScalarComparison.forget Λ S).obj L) :
  let VA := (RawModuleScalarComparison.forget Λ Y').mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus
  let LB := (upperStar (ModuleCat.{u + 1} Λ) h).obj L
  let cA := scalarSourceFactor Λ h' L E t
  let cB := scalarSourceFactor Λ h L E t
  let mS := moduleSourceFactor Λ a h h' w L
  let aS := abelianSourceFactor a h h' w E
  cA ≫ VA.map mS = aS ≫ H.map cB ≫
    (RawModuleScalarComparison.derivedPullbackIso Λ a).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj LB) := by sorry

end AlgebraicGeometry.Etale
