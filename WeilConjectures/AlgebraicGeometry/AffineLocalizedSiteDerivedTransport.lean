/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-! # Transport of derived sheaves to an affine localized site

Source: Stacks Project, Tag 06Z0, and restriction along an isomorphism of ringed spaces.
-/

@[expose] public section

universe u wS w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Restriction along the affine spectrum isomorphism and the over-site equivalence
induce an equivalence of derived sheaf categories, compatible with termwise tilde.
Source: Stacks Project, Tag 06Z0, affine identification, and Mathlib's overEquiv and
restrictFunctorComp. -/
theorem affine_localized_site_derived_transport (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U)
    [HasDerivedCategory.{wS} (SheafOfModules.{u}
      (moduleRings (Spec (X.presheaf.obj (.op U))).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ E : DerivedCategory (SheafOfModules.{u}
        (moduleRings (Spec (X.presheaf.obj (.op U))).toRingedSpace)) ≌
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)),
      Nonempty ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} (X.presheaf.obj (.op U)) ⥤
          SheafOfModules.{u}
            (moduleRings (Spec (X.presheaf.obj (.op U))).toRingedSpace))
          (tilde.functor (X.presheaf.obj (.op U)))) ⟨fun _ _ ↦ tilde.map_zero⟩
          (.up ℤ) ⋙ DerivedCategory.Q) ⋙ E.functor ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q)  := by
  let R := X.presheaf.obj (.op U)
  let S := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let F := Modules.restrictFunctor hU.isoSpec.hom
  let G := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk F G
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [R]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let E : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : CategoryTheory.Limits.HasBinaryBiproducts S :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  have : CategoryTheory.Limits.HasBinaryBiproducts D :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  have : CategoryTheory.Limits.PreservesBinaryBiproducts E.functor :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let Φ := E.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let Ψ := E.inverse.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let ec := E.mapHomologicalComplex (.up ℤ)
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_unit_of_unit Ψ ec.unitIso.hom ec.counitIso.inv
      (fun _ ↦ by dsimp [HomologicalComplex.quasiIso]; infer_instance)
      (fun _ ↦ by dsimp [HomologicalComplex.quasiIso]; infer_instance)
  let ED := E.functor.mapDerivedCategory
  have : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q ED :=
    CatCommSq.mk E.functor.mapDerivedCategoryFactors.symm
  have : ED.IsEquivalence := Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q ED
  refine ⟨ED.asEquivalence, ⟨?_⟩⟩
  let T := tilde.functor R
  have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : T.Additive := inferInstanceAs (tilde.functor R).Additive
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
      E.functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ E.functor)) (.up ℤ)) _


end AlgebraicGeometry.Scheme
