/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange

/-!
# Sheaves placed in degree zero and the restriction of scalars on homotopy categories

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `Res` the restriction of scalars of
étale sheaves along `ρ`. For a morphism of sheaves `g : 𝟙 ⟶ Res 𝟙`, the morphism `g[0]` of the
derived categories, read through the identifications `F[0] ≅ Qh(F[0])` and the comparison
`Res ∘ Qh ≅ Qh ∘ Res`, is `Qh` of `g[0]` on homotopy categories
(`AlgebraicGeometry.Etale.singleFunctorObjIsoQh_inv_comp_map_comp_factorsh`), together with the
descriptions of the identifications `𝟙[0] ≅ 𝟙` of the units through `Qh`.

Each instantiation of a general lemma on derived functors is stated as its own lemma, as their
combination is expensive for the kernel.
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

/-- The derived restriction of scalars of a sheaf placed in degree zero, at the unit. -/
lemma restrictScalars_mapDerivedCategorySingleFunctor_inv_app_comp_factors_hom_app :
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _)) =
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _)) :=
  Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app _ _

/-- A morphism of sheaves `g : 𝟙 ⟶ Res 𝟙` placed in degree zero, read through the
identifications `F[0] ≅ Qh(F[0])` and the comparison `Res ∘ Qh ≅ Qh ∘ Res`, is `Qh` of `g[0]` on
homotopy categories. -/
@[reassoc]
lemma singleFunctorObjIsoQh_inv_comp_map_comp_factorsh (g : 𝟙_ _ ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))) :
    (singleFunctorObjIsoQh (𝟙_ _)).inv ≫
        (DerivedCategory.singleFunctor _ 0).map g ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjIsoQh (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))).hom ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map g ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _))) := by
  have h₁ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have h₃ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
  have h₄ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have h₅ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) :
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategoryFactors (.up ℤ)).inv.app
        K = 𝟙 _ := rfl
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [singleFunctorObjIsoQh, DerivedCategory.singleFunctorIsoCompQ, Iso.trans_inv,
    Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Iso.refl_inv,
    Iso.refl_hom, NatTrans.id_app, h₁, h₂, h₃, h₄, h₅, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [Category.comp_id]
  rw [restrictScalars_mapDerivedCategorySingleFunctor_inv_app_comp_factors_hom_app,
    Functor.map_comp, Functor.map_comp]
  rfl

variable (Γ : Type (u + 1)) [CommRing Γ] in
/-- The inverse of the identification `𝟙[0] ≅ 𝟙` of the unit of `D(X_ét)`, through `Qh`. -/
lemma singleFunctorObjUnitIso_inv_eq :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Γ) X).inv =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Γ)) (.up ℤ))).hom ≫
        (singleFunctorObjIsoQh (𝟙_ _)).inv := by
  simp [singleFunctorObjUnitIso]

variable (Γ : Type (u + 1)) [CommRing Γ] in
/-- The identification `𝟙[0] ≅ 𝟙` of the unit of `D(X_ét)`, followed by the unit comparison of
`Qh`. -/
lemma singleFunctorObjUnitIso_hom_comp_ε :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Γ) X).hom ≫ ε DerivedCategory.Qh =
      (singleFunctorObjIsoQh (𝟙_ _)).hom ≫ DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Γ)) (.up ℤ))).inv := by
  simp [singleFunctorObjUnitIso]

/-- The naturality of the comparison `Res ∘ Qh ≅ Qh ∘ Res` at the unit comparison of the
quotient functor. -/
lemma derivedRestrictScalars_map_Qh_map_εIso_inv_comp_factorsh :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (DerivedCategory.Qh.map
        (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
    (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) ≫
      DerivedCategory.Qh.map (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).map (Functor.Monoidal.εIso (HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv) :=
  (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.naturality _

end AlgebraicGeometry.Etale
