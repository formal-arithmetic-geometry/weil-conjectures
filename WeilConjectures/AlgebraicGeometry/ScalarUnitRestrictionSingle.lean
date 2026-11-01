/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitInsertion
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction

/-! The restriction-form regular scalar unit on degree-zero objects. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option maxHeartbeats 4000000 in
-- Checking the normalized scalar adjunction unfolds several derived comparisons.
/-- Transposing the normalized regular scalar unit gives the ordinary restriction unit.
Source: scalar-unit insertion normalization, followed by the adjunction hom equivalence.
Proof: apply the scalar adjunction hom equivalence to scalarUnit_eq_adjointInsertion.
Naturality moves the source single/unit isomorphism across the adjunction unit.
Cancel that source isomorphism and the target exact-single comparison.
(blueprint: new-lem-coef-scalar-unit-restriction-single) -/
theorem scalarUnit_restriction_single
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app
        (Etale.constantComplex A T) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        ((Etale.ExceptionalCoefficients.unitIso φ T).hom ≫
          (Etale.constantComplexIsoSingleFunctor B T).hom) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _) =
    (Etale.constantComplexIsoSingleFunctor A T).hom ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ))  := by
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  have h := congrArg (ad.homEquiv _ _) (scalarUnit_eq_adjointInsertion φ T)
  rw [SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply] at h
  erw [ad.homEquiv_naturality_left] at h
  rw [Adjunction.homEquiv_unit] at h
  have hiA : (Etale.constantComplexIsoSingleFunctor A T).hom = 𝟙 _ := by
    exact Etale.singleFunctorObjUnitIso_inv (ModuleCat.{u + 1} A) T
  have hiB : (Etale.constantComplexIsoSingleFunctor B T).hom = 𝟙 _ := by
    exact Etale.singleFunctorObjUnitIso_inv (ModuleCat.{u + 1} B) T
  rw [SheafExactDegreeZero.single_unit_hom, SheafExactDegreeZero.single_unit_inv] at h
  erw [Category.id_comp, Category.comp_id] at h
  rw [hiA, hiB]
  erw [Category.id_comp, Category.comp_id]
  erw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

set_option maxHeartbeats 4000000 in
-- Composition coherence has large exact-single comparison terms.
end AlgebraicGeometry.Etale
