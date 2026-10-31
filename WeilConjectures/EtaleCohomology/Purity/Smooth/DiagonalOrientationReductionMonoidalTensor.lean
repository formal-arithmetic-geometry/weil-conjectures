/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalPullback

/-!
# The commutation of the reduction of coefficients with the derived pullback is monoidal

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel, `Ψ` the
derived extension of scalars and `e : U ⟶ X` a morphism of schemes. The commutation
`Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*` (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`) is
compatible with the tensor comparisons of `Ψ` and of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_app_tensor_comp`): through the
counits it is the underived commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U`
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_eq`), which is monoidal
(`AlgebraicGeometry.Etale.isMonoidal_extendScalarsUpperStarIso_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) {U X : Scheme.{u}}
  (e : U ⟶ X)

instance isIso_derivedExtendScalarsPullbackOfCounit :
    IsIso (derivedExtendScalarsPullbackOfCounit hρ ha e) := by
  rw [← derivedExtendScalarsPullbackMap_eq]
  infer_instance

/-- **The commutation of `Ψ` with the derived pullback is compatible with the tensor
comparisons** (in terms of the comparison of left derived functors): for `K, M ∈ D(X_ét, Λ)`,
`Ψ_U Le^*(K ⊗ᴸ M) ⟶ Le^*Ψ_X(K ⊗ᴸ M) ⟶ Le^*(Ψ_X K ⊗ᴸ Ψ_X M) ⟶ Le^*Ψ_X K ⊗ᴸ Le^*Ψ_X M` is
`Ψ_U Le^*(K ⊗ᴸ M) ⟶ Ψ_U(Le^* K ⊗ᴸ Le^* M) ⟶ Ψ_U Le^* K ⊗ᴸ Ψ_U Le^* M`, followed by the
commutations. -/
theorem derivedExtendScalarsPullbackOfCounit_app_tensor_comp
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
    (derivedExtendScalarsPullbackOfCounit hρ ha e).app (K ⊗ M) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparison.app K).app M) ≫
          ((((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedTensorComparison.app
            ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor.obj K)).app
            ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor.obj M)) =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          ((((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedTensorComparison.app K).app M) ≫
        ((Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedTensorComparison.app
          (L((e)^*[ModuleCat.{u + 1} Λ]).obj K)).app (L((e)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
          ((derivedExtendScalarsPullbackOfCounit hρ ha e).app K ⊗ₘ
            (derivedExtendScalarsPullbackOfCounit hρ ha e).app M) := by
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have := preservesKFlatQuasiIso_extendScalars hρ ha U
  letI : (Sheaf.extendScalars X.smallEtaleTopology ρ).LaxMonoidal := Functor.Monoidal.toLaxMonoidal
  letI : (Sheaf.extendScalars U.smallEtaleTopology ρ).LaxMonoidal := Functor.Monoidal.toLaxMonoidal
  letI : ((e)^*[ModuleCat.{u + 1} Λ]).LaxMonoidal := Functor.Monoidal.toLaxMonoidal
  letI : ((e)^*[ModuleCat.{u + 1} Λ']).LaxMonoidal := Functor.Monoidal.toLaxMonoidal
  have : NatTrans.IsMonoidal (extendScalarsUpperStarIso ρ e).symm.hom :=
    isMonoidal_extendScalarsUpperStarIso_inv ρ e
  -- the comparison `Ψ_X ⋙ Le^* ≅ L(F_X ⋙ e^*)`, through the counits
  let γ : derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) ≅
      (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctor :=
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ e) ≪≫
      (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso _ _).symm
  have hγ (P : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
      γ.hom.app (DerivedCategory.Qh.obj P) ≫
        (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙
          (e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app P =
      L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app P) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ']))
            (.up ℤ)).hom.app P) := by
    simp only [γ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.assoc]
    rw [← Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_comp_counit,
      Iso.inv_hom_id_app_assoc]
    have hn := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') e).hom.naturality
      ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app P)
    have hf : (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') e).hom.app
        (DerivedCategory.Qh.obj
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P)) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).mapDerivedCategoryFactorsh.hom.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P) =
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P) :=
      ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac _
    erw [← reassoc_of% hn]
    rw [reassoc_of% hf]
  have hα (P : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
      (asIso (derivedExtendScalarsPullbackOfCounit hρ ha e)).hom.app (DerivedCategory.Qh.obj P) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app P) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj P) =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app P) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app
          ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (extendScalarsUpperStarIso ρ e).symm.hom (.up ℤ)).app P) := by
    have h := derivedExtendScalarsPullbackOfCounit_app_Qh hρ ha e P
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      extendScalarsUpperStarHomotopyIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Functor.mapHomotopyCategoryCompIso_refl_inv_app,
      Category.id_comp, Category.comp_id] at h
    rw [asIso_hom, Iso.symm_hom]
    exact h
  have h := Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso
    (Sheaf.extendScalars X.smallEtaleTopology ρ) ((e)^*[ModuleCat.{u + 1} Λ'])
    ((e)^*[ModuleCat.{u + 1} Λ]) (Sheaf.extendScalars U.smallEtaleTopology ρ)
    (extendScalarsUpperStarIso ρ e).symm (asIso (derivedExtendScalarsPullbackOfCounit hρ ha e))
    γ.hom hα hγ K M
  rw [h, asIso_inv, asIso_hom, IsIso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale
