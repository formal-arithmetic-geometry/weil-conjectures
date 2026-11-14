/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCompNatIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-!
# The projection map under a flat change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that every coefficient change
`a_X : Λ_X ⟶ Λ'_X` is flat, write `T = L(Ext_a) = Λ' ⊗ᴸ_Λ -` for the derived extensions of
scalars, and let `f : X ⟶ Y` be a morphism of schemes. The extensions of scalars are strong
monoidal (`Functor.leftDerivedTensorComparison`), and the derived (Pull) isomorphism
`Lf^* ⋙ T ≅ T ⋙ Lf^*` (`ProEtale.CondensedRing.derivedPullIso`) is compatible with these tensor
comparisons and those of the derived pullbacks
(`ProEtale.CondensedRing.comparisonCompatible_derivedPullIso`): it is induced by the underived
(Pull) isomorphism, which is monoidal. Its mate along the adjunctions `Lf^* ⊣ Rf_*` is the (Push)
comparison `T Rf_* ⟶ Rf_* T` (`ProEtale.CondensedRing.derivedPushHom`). Hence `T` carries the
projection map `Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)` with coefficients `Λ` to the projection map
with coefficients `Λ'` at `(T K, T M)`, up to (Push) at `K` and at `K ⊗ᴸ Lf^* M`
(`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`). In particular the
projection formula with coefficients `Λ'` holds at `(T K, T M)` as soon as it holds with
coefficients `Λ` at `(K, M)` and (Push) is invertible at `K` and at `K ⊗ᴸ Lf^* M`
(`ProEtale.CondensedRing.isIso_projectionMap_app_app_extendScalars`).

This is the formal part of blueprint `proposition-proper-direct-image-constructible-complexes` (3),
deducing the projection formula with coefficients `E` and `ℚ̄_ℓ` from the one with coefficients
`𝒪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The tensor comparison `T(K ⊗ᴸ M) ≅ T K ⊗ᴸ T M` of the derived extension of scalars
`T = L(Ext_{a_X})`, as an isomorphism of bifunctors: the tensor comparison
`Functor.leftDerivedTensorComparison` of the strong monoidal functor `Ext_{a_X}`
(`Mod.extendScalarsMonoidal`). -/
noncomputable def derivedExtendScalarsTensorIso (X : Scheme.{u}) :
    (Functor.postcompose₂.obj (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
        (curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)))) ≅
      (((Functor.whiskeringLeft₂ _).obj
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).obj
          (curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj Λ' X)))) :=
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  asIso (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 4000000 in
-- the derived categories of module objects are unfolded when matching the comparisons
/-- The derived (Pull) isomorphism `Lf^* ⋙ T ≅ T ⋙ Lf^*` is compatible with the tensor
comparisons of the derived pullbacks (`leftDerivedUpperStarTensor`) and of the derived extensions
of scalars (`derivedExtendScalarsTensorIso`): it is the isomorphism of composites of left derived
functors induced by the underived (Pull) isomorphism
(`derivedPullIso_eq_leftDerivedFunctorCompNatIso`), which is monoidal
(`isMonoidal_pullIso_hom`), so this is
`Functor.map_leftDerivedTensorComparison_comp_eq_of_iso`. -/
theorem comparisonCompatible_derivedPullIso :
    Adjunction.ComparisonCompatible (derivedPullIso a f).symm
      (leftDerivedUpperStarTensor Λ f) (leftDerivedUpperStarTensor Λ' f)
      (derivedExtendScalarsTensorIso a X) (derivedExtendScalarsTensorIso a Y) := by
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a Y)
  have := isMonoidal_pullIso_hom a f
  intro K M
  have h := Functor.map_leftDerivedTensorComparison_comp_eq_of_iso
    (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ (f)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X)) (pullIso a f) K M
  rw [← derivedPullIso_eq_leftDerivedFunctorCompNatIso] at h
  rw [leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  simp only [derivedExtendScalarsTensorIso, asIso_hom, Iso.symm_inv, Iso.symm_hom,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map, Functor.comp_obj]
  rw [reassoc_of% h, Iso.hom_inv_id_app_assoc, ← MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]

set_option maxHeartbeats 2000000 in
-- unifying the projection maps with `Adjunction.rightAdjointProjectionMap` unfolds the derived
-- categories of module objects
/-- **The projection formula under a flat change of coefficients**: if the projection map
`Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)` with coefficients `Λ` is an isomorphism at `(K, M)` and the
(Push) comparison `T Rf_* ⟶ Rf_* T` is an isomorphism at `K` and at `K ⊗ᴸ Lf^* M`, then the
projection map with coefficients `Λ'` is an isomorphism at `(T K, T M)`. -/
theorem isIso_projectionMap_app_app_extendScalars
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    [IsIso (((projectionMap Λ f).app K).app M)]
    [IsIso ((derivedPushHom a f).app K)]
    [IsIso ((derivedPushHom a f).app
      (((curriedTensor _).obj K).obj (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M)))] :
    IsIso (((projectionMap Λ' f).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)).app
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) := by
  have hβ : mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ' f) (derivedPullIso a f).symm.hom =
        derivedPushHom a f :=
    (derivedPushHom_eq_mateEquiv a f).symm
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ' f) (derivedPullIso a f).symm.hom).app K) := by
    rw [hβ]
    infer_instance
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ' f) (derivedPullIso a f).symm.hom).app
        (((curriedTensor _).obj K).obj (((f)^*⟦Λ⟧).leftDerivedFunctor.obj M))) := by
    rw [hβ]
    infer_instance
  have h₀ : IsIso ((((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
      (leftDerivedUpperStarTensor Λ f)).app K).app M) :=
    (inferInstance : IsIso (((projectionMap Λ f).app K).app M))
  exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ' f)
    (comparisonCompatible_derivedPullIso a f) K M

end AlgebraicGeometry.ProEtale.CondensedRing
