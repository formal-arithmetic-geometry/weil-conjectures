/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.EtaleScalarUnitInsertion
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.CategoryTheory.NormalizedScalarUnitAdjunction

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
/-- The regular scalar unit remains its ordinary sheaf map after another scalar restriction.
Source: exact-single functor coherence and the preceding adjunction transpose calculation.
Proof: move the target single/unit isomorphism through the restriction compositor by
naturality. Apply scalarUnit_restriction_single, then the exact-single compositor
identity and naturality for the ordinary lax restriction unit.
(blueprint: new-lem-coef-scalar-unit-restriction-single) -/
theorem scalarUnit_restriction_comp_single
    {R A B : Type (u + 1)} [CommRing R] [CommRing A] [CommRing B]
    (φ : R →+* A) (ψ : A →+* B) (χ : R →+* B) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ)).unit.app
            (Etale.constantComplex A T) ≫
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ).map
            (Etale.ExceptionalCoefficients.unitIso ψ T).hom) ≫
      (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology hχ).hom.app
        (Etale.constantComplex B T) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology χ).map
        (Etale.constantComplexIsoSingleFunctor B T).hom ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology χ).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _) =
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (Etale.constantComplexIsoSingleFunctor A T).hom ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).map
            (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology ψ)) ≫
          (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ hχ).hom.app (𝟙_ _)) := by
  let J := T.smallEtaleTopology
  let U := Sheaf.restrictScalars J φ
  let V := Sheaf.restrictScalars J ψ
  let W := Sheaf.restrictScalars J χ
  let α := Sheaf.derivedRestrictScalarsCompIso J hχ
  let e := Sheaf.restrictScalarsCompIso J φ ψ χ hχ
  let iA := Etale.constantComplexIsoSingleFunctor A T
  let iB := Etale.constantComplexIsoSingleFunctor B T
  let η := (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J ψ)).unit.app
    (Etale.constantComplex A T)
  let lam := (Etale.ExceptionalCoefficients.unitIso ψ T).hom
  let ε := Functor.LaxMonoidal.ε V
  have hs : η ≫ V.mapDerivedCategory.map lam ≫ V.mapDerivedCategory.map iB.hom =
      iA.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ε ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app (𝟙_ _) := by
    dsimp only [η, V, J, iA, iB, ε, lam]
    apply (cancel_mono
      (((Sheaf.restrictScalars T.smallEtaleTopology ψ).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ _))).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
    exact (by simpa only [Functor.map_comp, Category.assoc] using
      scalarUnit_restriction_single ψ T)
  have hc : U.mapDerivedCategory.map
        ((V.mapDerivedCategorySingleFunctor 0).inv.app (𝟙_ _)) ≫
      α.hom.app ((_root_.DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≫
        (W.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) =
      (U.mapDerivedCategorySingleFunctor 0).hom.app (V.obj (𝟙_ _)) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (e.hom.app (𝟙_ _)) := by
    apply (cancel_epi
      ((U.mapDerivedCategorySingleFunctor 0).inv.app (V.obj (𝟙_ _)))).1
    dsimp only [α, Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    simp only [Category.assoc]
    erw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
      ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor V U (𝟙_ _)]
    dsimp only [U, V]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  change U.mapDerivedCategory.map (η ≫ V.mapDerivedCategory.map lam) ≫
      α.hom.app _ ≫ W.mapDerivedCategory.map iB.hom ≫
        (W.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) = _
  erw [← reassoc_of% (α.hom.naturality iB.hom)]
  erw [← Functor.map_comp_assoc]
  change U.mapDerivedCategory.map
      ((η ≫ V.mapDerivedCategory.map lam) ≫ V.mapDerivedCategory.map iB.hom) ≫
      α.hom.app _ ≫ (W.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) = _
  erw [Category.assoc, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  rw [← reassoc_of% ((U.mapDerivedCategorySingleFunctor 0).hom.naturality ε)]

end AlgebraicGeometry.Etale
