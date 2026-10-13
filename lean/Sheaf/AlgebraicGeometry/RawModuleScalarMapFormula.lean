/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

-- Reuse the raw cohomology API's cached module-sheaf instances.

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


attribute [local instance] moduleSheafCategory moduleSheafPreadditive moduleSheafAbelian
  moduleSheafHasDerivedCategory

/-- Evaluation of the explicit additive scalar Hom map.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-map-formula).

Proof: Expand the definition of rawModuleAbelianHomMap. Its additive map is the composite of
derived forgetting, right composition by the coefficient factor, and left composition by the
source factor. Evaluation of AddCommGrpCat.ofHom and of the two additive compositions therefore
gives c composed with V(z) composed with b. The two named factor definitions have exactly these
source and coefficient bodies. No naturality or coherence equation is used. This applies to zero
classes, zero sheaves, identity geometric maps and degree zero. -/
theorem rawModuleScalar_map_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawModuleAbelianHomMap Λ k G q U A z =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map z ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rfl

end AlgebraicGeometry.Etale
