/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! Ordinary coefficient-unit normalization before site comparison.
(blueprint: lem-sp-general-ring-ordinary-scalar-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem singleUnit_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom = 𝟙 _ := by
  have h := (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom_inv_id
  rw [Etale.singleFunctorObjUnitIso_inv] at h
  exact (Category.comp_id _).symm.trans h

/-- The single-functor unit conversions cancel from the ordinary scalar-unit map.
Source: the actual derived coefficient-unit model, general-ring purity (1)
(blueprint: lem-sp-general-ring-ordinary-scalar-unit). -/
theorem ordinaryScalarUnitSandwich
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    ((Etale.scalarExtension φ T).mapIso
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
      Etale.ExceptionalCoefficients.unitIso φ T ≪≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm).hom =
        (Etale.ExceptionalCoefficients.unitIso φ T).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [singleUnit_hom A T, (Etale.scalarExtension φ T).map_id,
    Etale.singleFunctorObjUnitIso_inv]
  exact (Category.id_comp _).trans (Category.comp_id _)

end AlgebraicGeometry.ProEtale
