/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitPullback
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeConstant
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeFactorshUnit
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange

/-!
# The unit comparison of the reduction of coefficients as a change of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and `Ψ`
the derived extension of scalars. The unit comparison `Ψ Λ_X ≅ Λ'_X` of the monoidal functor `Ψ`
is the adjoint, under `Ψ ⊣ Res`, of any morphism `c : Λ_X ⟶ Res Λ'_X` which is induced on
homotopy categories by the adjoint of the unit comparison of the extension of scalars of
complexes (`AlgebraicGeometry.Etale.derivedExtendScalarsUnitIso_hom_eq_homEquiv_symm`).
-/

@[expose] public section

universe u


open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

variable (ρ) in
/-- The unit `𝟙 ⟶ Res(F 𝟙) ⟶ Res 𝟙` of the extension of scalars of complexes, on homotopy
categories: the adjoint of the unit comparison `F 𝟙 ⟶ 𝟙`. -/
noncomputable def extendScalarsHomotopyUnitMap :
    𝟙_ (HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) ⟶
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj (𝟙_ _) :=
  (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).homEquiv
    _ _) (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))

variable (ρ) in
/-- `F` of the unit map `𝟙 ⟶ Res 𝟙` followed by the counit is the unit comparison of `F`. -/
lemma map_extendScalarsHomotopyUnitMap_comp_counit :
    ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (extendScalarsHomotopyUnitMap ρ X) ≫
      ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).counit.app (𝟙_ _) =
      η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) := by
  have h := (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
    (.up ℤ)).homEquiv _ _).symm_apply_apply
      (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- **The unit comparison of `Ψ` as an adjoint**: if `c : Λ_X ⟶ Res Λ'_X` is induced on homotopy
categories by the unit map `𝟙 ⟶ Res 𝟙` (`AlgebraicGeometry.Etale.extendScalarsHomotopyUnitMap`),
the unit comparison `Ψ Λ_X ≅ Λ'_X` is the adjoint of `c`. -/
lemma derivedExtendScalarsUnitIso_hom_eq_homEquiv_symm
    (c : 𝟙_ _ ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (𝟙_ _))
    (hc : c ≫ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map (extendScalarsHomotopyUnitMap ρ X)) :
    (derivedExtendScalarsUnitIso hρ ha X).hom =
      ((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm c := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  have hΨ := leftDerivedFunctor_extendScalars_η_comp_ε hρ ha X
  have hcnt := derivedExtendScalarsAdjunction_counit_app_Qh hρ ha X (𝟙_ _)
  have hn₁ := (derivedExtendScalarsAdjunction hρ ha X).counit.naturality (ε DerivedCategory.Qh)
  have hn₂ := (derivedExtendScalarsCounit hρ ha X).naturality (extendScalarsHomotopyUnitMap ρ X)
  have hu := congrArg DerivedCategory.Qh.map (map_extendScalarsHomotopyUnitMap_comp_counit ρ X)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn₁ hn₂
  simp only [Functor.map_comp] at hu
  rw [Adjunction.homEquiv_counit, ← cancel_mono (ε DerivedCategory.Qh), Category.assoc, ← hn₁,
    hcnt]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hc,
    Functor.map_comp_assoc, reassoc_of% hn₂, hu, derivedExtendScalarsUnitIso_hom, hΨ]
  rfl

variable (ρ) in
/-- The unit `𝟙 ⟶ Res(F 𝟙) ⟶ Res 𝟙` of the extension of scalars of étale sheaves: the adjoint of
the unit comparison `F 𝟙 ⟶ 𝟙`. -/
noncomputable def extendScalarsUnitMap :
    𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj (𝟙_ _) :=
  ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _)
    (η (Sheaf.extendScalars X.smallEtaleTopology ρ))

variable (ρ) in
/-- The unit `𝟙 ⟶ Res 𝟙` on cochain complexes is the unit map of sheaves placed in degree zero. -/
lemma mapHomologicalComplex_unit_app_unit_comp_map_η_extendScalars :
    (Adjunction.mapHomologicalComplex (.up ℤ)
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).unit.app
        (𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ))) =
    (HomologicalComplex.single _ (.up ℤ) 0).map (extendScalarsUnitMap ρ X) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplex_η,
    Functor.mapCochainComplexεIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, extendScalarsUnitMap,
    Adjunction.homEquiv_unit, Functor.Monoidal.εIso_inv, Functor.map_comp, Category.assoc,
    Iso.app_hom, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  have hn := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom
  exact (Category.assoc _ _ _).symm.trans (hn =≫ _).symm

variable (ρ) in
/-- The unit of the adjunction on homotopy categories at the unit is the image of the unit of the
adjunction on cochain complexes. -/
lemma mapHomotopyCategory_extendScalarsAdjunction_unit_app_unit :
    ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).unit.app (𝟙_ _) =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((Adjunction.mapHomologicalComplex (.up ℤ)
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).unit.app
        (𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ))) :=
  Adjunction.mapHomotopyCategory_unit_app_quotient _ _ _

variable (ρ) in
/-- The restriction of scalars of the unit comparison of `F` on homotopy categories is the image
of the one on cochain complexes. -/
lemma mapHomotopyCategory_map_η_extendScalars :
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)))) :=
  rfl

variable (ρ) in
/-- The unit map `𝟙 ⟶ Res 𝟙` on homotopy categories, as the unit followed by `Res η`. -/
lemma extendScalarsHomotopyUnitMap_eq_unit_comp :
    extendScalarsHomotopyUnitMap ρ X =
      ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).unit.app (𝟙_ _) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) :=
  Adjunction.homEquiv_unit _ _ _ _

variable (ρ) in
/-- The unit map `𝟙 ⟶ Res 𝟙` on homotopy categories is the unit map of sheaves placed in
degree zero. -/
lemma extendScalarsHomotopyUnitMap_eq :
    extendScalarsHomotopyUnitMap ρ X =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map (extendScalarsUnitMap ρ X) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _)) := by
  rw [extendScalarsHomotopyUnitMap_eq_unit_comp,
    mapHomotopyCategory_extendScalarsAdjunction_unit_app_unit,
    mapHomotopyCategory_map_η_extendScalars, ← Functor.map_comp,
    mapHomologicalComplex_unit_app_unit_comp_map_η_extendScalars]

variable (ρ) in
/-- The constant sheaves placed in degree zero: a morphism of sheaves `g : 𝟙 ⟶ Res 𝟙` placed in
degree zero, read through the identifications of the units of the derived categories, is `g`
placed in degree zero on homotopy categories. -/
lemma singleFunctorObjUnitIso_inv_comp_map_comp_factorsh (g : 𝟙_ _ ⟶
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
  singleFunctorObjUnitIso_inv_comp_map_comp_factorsh_eq ρ X g

variable (ρ) in
/-- The change of coefficients `Λ ⊗ ℤ ⟶ Res(Λ' ⊗ ℤ)` of the constant sheaves is the unit map
`𝟙 ⟶ Res 𝟙`. -/
lemma extendScalarsConstantZModIso_inv_comp_extendScalarsChangeMap_app :
    (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv ≫
        (extendScalarsChangeMap ρ X).app X.constantSheafInt ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
          (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom =
      extendScalarsUnitMap ρ X := by
  exact extendScalarsConstantZModIso_inv_comp_changeMap_app_comp ρ X

/-- The identification `Λ_X ≅ (Λ ⊗ ℤ)[0]` pulled back from `Spec ℤ[1/n]` is the direct one. -/
lemma constantComplexIsoSingleFunctorExtendScalarsInt_eq_ofUnit (Γ : Type (u + 1)) [CommRing Γ]
    [HasInvertibleExponent Γ X] :
    constantComplexIsoSingleFunctorExtendScalarsInt X Γ =
      constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Γ :=
  constantComplexIsoSingleFunctorExtendScalarsInt_eq_constantComplexIsoOfUnit Γ X


end AlgebraicGeometry.Etale
