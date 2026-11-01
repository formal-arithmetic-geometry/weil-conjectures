/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeFactorsh

/-!
# The unit of the derived categories and the restriction of scalars

For a morphism of étale sheaves `g : 𝟙 ⟶ Res 𝟙`, the morphism `g[0]` read through the
identifications `𝟙[0] ≅ 𝟙` of the units of the derived categories and the comparison
`Res ∘ Qh ≅ Qh ∘ Res` is `ε Qh` followed by `Qh` of `g[0]` on homotopy categories
(`AlgebraicGeometry.Etale.singleFunctorObjUnitIso_inv_comp_map_comp_factorsh_eq`). The steps are
separate lemmas, combined by whiskering, to keep the kernel cost low.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The first step: the unit of `D(X_ét, Λ)` through `Qh`. -/
lemma singleFunctorObjUnitIso_inv_comp_map_comp_factorsh_eq₁ (g : 𝟙_ _ ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))) :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map g ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom ≫
        (singleFunctorObjIsoQh (𝟙_ _)).inv ≫
        (DerivedCategory.singleFunctor _ 0).map g ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app
          (𝟙_ _) := by
  rw [singleFunctorObjUnitIso_inv_eq, Category.assoc, Category.assoc]

/-- The second step: the unit of `D(X_ét, Λ')` through `Qh`. -/
lemma derivedRestrictScalars_map_singleFunctorObjUnitIso_hom_comp_factorsh :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjIsoQh (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))).hom ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) ≫
        DerivedCategory.Qh.map (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory
          (.up ℤ)).map (Functor.Monoidal.εIso (HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv) := by
  rw [← Functor.map_comp_assoc, singleFunctorObjUnitIso_hom_comp_ε, Functor.map_comp_assoc,
    derivedRestrictScalars_map_Qh_map_εIso_inv_comp_factorsh]

/-- The last step: the unit comparisons of the quotient functors are identities. -/
lemma Qh_map_εIso_hom_comp_Qh_map_comp_Qh_map_εIso_inv
    (x : (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) :
    DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map x) ≫
      DerivedCategory.Qh.map (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory
          (.up ℤ)).map (Functor.Monoidal.εIso (HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map x) := by
  have hε : (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom = 𝟙 _ := rfl
  have hε' : (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv = 𝟙 _ := rfl
  rw [hε, hε']
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
/-- The constant sheaves placed in degree zero: a morphism of sheaves `g : 𝟙 ⟶ Res 𝟙` placed in
degree zero, read through the identifications of the units of the derived categories, is `g`
placed in degree zero on homotopy categories. -/
lemma singleFunctorObjUnitIso_inv_comp_map_comp_factorsh_eq (g : 𝟙_ _ ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))) :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map g ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map g ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _))) :=
  ((singleFunctorObjUnitIso_inv_comp_map_comp_factorsh_eq₁ ρ X g).trans
    (ε DerivedCategory.Qh ≫= DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom ≫=
      (singleFunctorObjIsoQh (𝟙_ _)).inv ≫= (DerivedCategory.singleFunctor _ 0).map g ≫=
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫=
      derivedRestrictScalars_map_singleFunctorObjUnitIso_hom_comp_factorsh ρ X)).trans
  ((ε DerivedCategory.Qh ≫= DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom ≫=
      singleFunctorObjIsoQh_inv_comp_map_comp_factorsh_assoc ρ X g _).trans
    (ε DerivedCategory.Qh ≫= Qh_map_εIso_hom_comp_Qh_map_comp_Qh_map_εIso_inv ρ X _))

end AlgebraicGeometry.Etale
