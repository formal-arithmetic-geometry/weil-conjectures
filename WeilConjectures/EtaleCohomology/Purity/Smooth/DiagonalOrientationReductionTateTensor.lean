/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalPullback

/-!
# The commutation of the reduction of coefficients with the derived pullback is monoidal

test
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.NatTrans.IsMonoidal

variable {C D D' E : Type*} [Category* C] [Category* D] [Category* D'] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory D'] [MonoidalCategory E]
  {F₁ : C ⥤ D} {F₂ : D ⥤ E} {G₁ : C ⥤ D'} {G₂ : D' ⥤ E} [F₁.Monoidal] [F₂.Monoidal]
  [G₁.Monoidal] [G₂.Monoidal]

/-- A natural transformation between composites of monoidal functors which is monoidal for the
lax structures of the composite monoidal structures is monoidal for the composite lax
structures. -/
lemma of_instComp (τ : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (h : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ τ (Functor.Monoidal.instComp _ _).toLaxMonoidal
      (Functor.Monoidal.instComp _ _).toLaxMonoidal) : NatTrans.IsMonoidal τ :=
  h

end CategoryTheory.NatTrans.IsMonoidal

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) {U X : Scheme.{u}}
  (e : U ⟶ X)

/-- The left derived functor of `F_X ⋙ e^*` is `Ψ_X ⋙ Le^*`, the pullback being exact. -/
noncomputable def extendScalarsUpperStarLeftDerivedIso :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctor ≅
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor ⋙
        L((e)^*[ModuleCat.{u + 1} Λ']) :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ e).symm

set_option profiler true in
/-- `extendScalarsUpperStarLeftDerivedIso` is compatible with the counits. -/
lemma extendScalarsUpperStarLeftDerivedIso_inv_app_comp_counit
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    (extendScalarsUpperStarLeftDerivedIso hρ ha e).inv.app (DerivedCategory.Qh.obj K) ≫
        (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙
          (e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app K =
      L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app K) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙
            (e)^*[ModuleCat.{u + 1} Λ'])) (.up ℤ)).hom.app K) := by
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  have h₁ := Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_comp_counit
    (Sheaf.extendScalars X.smallEtaleTopology ρ) (e)^*[ModuleCat.{u + 1} Λ'] K
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') e).inv.naturality
    ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app K)
  have h₃ := Functor.leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit
    (e)^*[ModuleCat.{u + 1} Λ']
    (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K)
  rw [← h₁]
  simp only [extendScalarsUpperStarLeftDerivedIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← h₃]
  simp only [Category.assoc]
  erw [reassoc_of% h₂]
  rw [Iso.hom_inv_id_app_assoc]


set_option profiler true in
/-- The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` through the counits. -/
lemma derivedExtendScalarsPullbackIso_hom_app_Qh_comp_counit
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
    (derivedExtendScalarsPullbackIso hρ ha e).hom.app (DerivedCategory.Qh.obj K) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app K) ≫
          ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
            (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K) =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app K) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app
          ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (extendScalarsUpperStarIso ρ e).symm.hom (.up ℤ)).app K) := by
  have h := derivedExtendScalarsPullbackOfCounit_app_Qh hρ ha e K
  have h' : (extendScalarsUpperStarHomotopyIso ρ e).inv.app K =
      (NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).symm.hom (.up ℤ)).app K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    simp only [extendScalarsUpperStarHomotopyIso, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
      Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj,
      Functor.mapHomotopyCategoryCompIso_inv_app_quotient_obj, Iso.symm_hom,
      ]
    have hq : (NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).inv (.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj K) = (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (extendScalarsUpperStarIso ρ e).inv (.up ℤ)).app K) :=
      rfl
    rw [hq, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
  rw [h'] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [derivedExtendScalarsPullbackIso_hom, derivedExtendScalarsPullbackMap_eq]
  exact h

set_option profiler true in
/-- **The commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` is compatible with the tensor comparisons**,
written with the tensor comparisons of the left derived functors
(`CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso`). -/
theorem derivedExtendScalarsPullbackIso_leftDerivedTensorComparison
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
    L((e)^*[ModuleCat.{u + 1} Λ']).map
        (((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparison.app K).app M) ≫
        ((((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedTensorComparison.app
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor.obj K)).app
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor.obj M)) =
      (derivedExtendScalarsPullbackIso hρ ha e).inv.app (K ⊗ M) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          ((((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedTensorComparison.app K).app M) ≫
        ((Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedTensorComparison.app
          (L((e)^*[ModuleCat.{u + 1} Λ]).obj K)).app (L((e)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
          ((derivedExtendScalarsPullbackIso hρ ha e).hom.app K ⊗ₘ
            (derivedExtendScalarsPullbackIso hρ ha e).hom.app M) := by
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
  have := NatTrans.IsMonoidal.of_instComp (extendScalarsUpperStarIso ρ e).symm.hom
    (isMonoidal_extendScalarsUpperStarIso_inv ρ e)
  exact Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso
    (Sheaf.extendScalars X.smallEtaleTopology ρ) (e)^*[ModuleCat.{u + 1} Λ']
    (e)^*[ModuleCat.{u + 1} Λ] (Sheaf.extendScalars U.smallEtaleTopology ρ)
    (extendScalarsUpperStarIso ρ e).symm (derivedExtendScalarsPullbackIso hρ ha e)
    (extendScalarsUpperStarLeftDerivedIso hρ ha e).inv
    (derivedExtendScalarsPullbackIso_hom_app_Qh_comp_counit hρ ha e)
    (extendScalarsUpperStarLeftDerivedIso_inv_app_comp_counit hρ ha e) K M
end AlgebraicGeometry.Etale
