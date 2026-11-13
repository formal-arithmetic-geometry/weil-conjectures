/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import WeilConjectures.AlgebraicGeometry.AffineKoszulSectionRoof
import WeilConjectures.AlgebraicGeometry.TensorRoofTransposition

/-! # Koszul tensor roof lifting an affine open morphism

## References

* Stacks Project, Tag 08EH
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 400000 in
-- Keep tensor instances as local abbreviations during the representative computation.
private theorem affinePerfectTensorRoof_aux
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    let := SheafOfModules.monoidalCategory X.sheaf
    let := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  let H := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf).obj (Opposite.op A, E'.obj)
  have hH : schemeDerivedQCohProperty X H :=
    rhom_supported_quasiCoherent_perfect_part X A E'.obj E'.property hA
  obtain ⟨e, he⟩ := tensor_roof_transposition X U A E'.obj P hP eA
  obtain ⟨J, hJ, hperfect, u, ξ, hu, hξ⟩ :=
    affine_koszul_section_roof X U hU ⟨H, hH⟩ (e.symm α)
  obtain ⟨γ, hβ, hγ⟩ := he J hJ u hu ξ (e.symm α) hξ
  let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
  let β : B ⟶ A := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
    DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
  have : IsIso (R.map β) := hβ
  refine ⟨J, hJ, hperfect, u, γ, asIso (R.map β), rfl, ?_⟩
  change α = (asIso (R.map β)).inv ≫ R.map γ
  have hγ' : R.map β ≫ α = R.map γ := by
    simpa only [Equiv.apply_symm_apply] using hγ
  rw [← hγ']
  simp

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- The Koszul roof and the lifted map for a fixed K-flat model of the source
(Stacks, Tag 08EH). -/
theorem exists_affine_perfect_tensor_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ := by
  exact affinePerfectTensorRoof_aux X U hU E' A hA α P hP eA

end AlgebraicGeometry.Scheme
