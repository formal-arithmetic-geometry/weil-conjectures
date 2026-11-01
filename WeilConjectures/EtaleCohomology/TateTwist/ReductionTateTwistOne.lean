/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionSingle

/-!
# The reduction of the Tate twist `Λ(1)`

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel,
with characteristics `n = n' e` (for instance the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`, `e = ℓ`),
and `Ψ` the derived extension of scalars along `ρ`. The change of coefficients
`Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate twists (`AlgebraicGeometry.Etale.tateTwistObjectOneChangeMap`,
the `e`-th power map `μ_n ⟶ μ_{n'}`) is adjoint to an isomorphism `Ψ(Λ_X(1)) ≅ Λ'_X(1)`
(`AlgebraicGeometry.Etale.isIso_homEquiv_symm_tateTwistObjectOneChangeMap`): `Λ_X(1)` is a flat
sheaf in degree zero, whose derived extension of scalars is `Λ' ⊗_Λ (μ_n ⊗ Λ) = μ_n ⊗ Λ'`, and the
power map `μ_n ⊗ Λ' ⟶ μ_{n'} ⊗ Λ'` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_extendScalars_map_rootsOfUnityPow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The extension of scalars `Λ' ⊗_Λ (Λ ⊗ F) ≅ Λ' ⊗ F` of étale sheaves of abelian groups `F`:
the two functors are left adjoint to the forgetful functor from sheaves of `Λ'`-modules. -/
noncomputable def extendScalarsCompExtendScalarsIso :
    extendScalars Λ X ⋙ Sheaf.extendScalars X.smallEtaleTopology ρ ≅ extendScalars Λ' X :=
  Adjunction.leftAdjointUniq
    ((extendScalarsAdjunction Λ X).comp (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ))
    ((extendScalarsAdjunction Λ' X).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

lemma extendScalarsChangeMap_app (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsChangeMap ρ X).app F = ((extendScalarsAdjunction Λ X).homEquiv F
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj ((extendScalars Λ' X).obj F))).symm
      ((extendScalarsAdjunction Λ' X).unit.app F) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The change of coefficients `Λ ⊗ F ⟶ Res (Λ' ⊗ F)` is adjoint to the identification
`Λ' ⊗_Λ (Λ ⊗ F) ≅ Λ' ⊗ F`. -/
lemma homEquiv_symm_extendScalarsChangeMap_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _).symm
        ((extendScalarsChangeMap ρ X).app F) =
      (extendScalarsCompExtendScalarsIso ρ X).hom.app F := by
  apply (((extendScalarsAdjunction Λ X).comp
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).homEquiv _ _).injective
  rw [extendScalarsCompExtendScalarsIso, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have h₁ : (((extendScalarsAdjunction Λ X).comp
      (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).homEquiv _ _)
        (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _).symm
          ((extendScalarsChangeMap ρ X).app F)) =
      (extendScalarsAdjunction Λ X).homEquiv F
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj ((extendScalars Λ' X).obj F))
        ((extendScalarsChangeMap ρ X).app F) := by
    rw [Adjunction.comp_homEquiv]
    exact congrArg ((extendScalarsAdjunction Λ X).homEquiv _ _) (Equiv.apply_symm_apply _ _)
  have h₂ : (extendScalarsAdjunction Λ X).homEquiv F
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj ((extendScalars Λ' X).obj F))
        ((extendScalarsChangeMap ρ X).app F) = (extendScalarsAdjunction Λ' X).unit.app F := by
    rw [extendScalarsChangeMap_app, Equiv.apply_symm_apply]
  have h₃ : ((extendScalarsAdjunction Λ' X).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) :
        sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat.{u + 1}) ≅
          Sheaf.restrictScalars X.smallEtaleTopology ρ ⋙ sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).unit.app F =
      (extendScalarsAdjunction Λ' X).unit.app F := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
    exact Category.comp_id _
  exact h₁.trans (h₂.trans h₃.symm)

variable {X} in
/-- The power map `μ_c ⟶ μ_a`, `c = a b`, becomes an isomorphism after extending the
coefficients to a ring `Λ` in which `a` vanishes, when `c` is invertible on `X`. -/
lemma isIso_extendScalars_map_rootsOfUnityPow' (Λ : Type (u + 1)) [CommRing Λ] (a b c : ℕ)
    (h : c = a * b) (ha : (a : Λ) = 0) (hc : IsUnit (c : Γ(X, ⊤))) :
    IsIso ((extendScalars Λ X).map (rootsOfUnityPow a b c h)) := by
  subst h
  exact isIso_extendScalars_map_rootsOfUnityPow Λ a b ha hc

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'}
  (hρ : Function.Surjective ρ) {a : Λ} (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] [NeZero (ringChar Λ)]
  [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)

/-- The adjoint `Λ' ⊗_Λ Λ_X(1) ⟶ μ_{n'} ⊗ Λ'` of the change of coefficients of the Tate sheaves:
`Λ' ⊗_Λ (μ_n ⊗ Λ) ≅ μ_n ⊗ Λ'` followed by the `e`-th power map. -/
noncomputable def tateTwistSheafOneReductionMap :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).obj (tateTwistSheaf Λ X 1) ⟶
      (extendScalars Λ' X).obj (X.rootsOfUnitySheaf (ringChar Λ')) :=
  (Sheaf.extendScalars X.smallEtaleTopology ρ).map
      ((tateTwistSheafOneIso X Λ).hom ≫ (extendScalars Λ X).map (rootsOfUnityPow _ e _ he)) ≫
    (extendScalarsCompExtendScalarsIso ρ X).hom.app _

instance isIso_tateTwistSheafOneReductionMap :
    IsIso (tateTwistSheafOneReductionMap X e he (ρ := ρ)) := by
  have hn : (Sheaf.extendScalars X.smallEtaleTopology ρ).map
      ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he)) ≫
        (extendScalarsCompExtendScalarsIso ρ X).hom.app _ =
      (extendScalarsCompExtendScalarsIso ρ X).hom.app _ ≫
        (extendScalars Λ' X).map (rootsOfUnityPow _ e _ he) :=
    (extendScalarsCompExtendScalarsIso ρ X).hom.naturality (rootsOfUnityPow _ e _ he)
  have := isIso_extendScalars_map_rootsOfUnityPow' (X := X) Λ' _ e _ he ringChar.Nat.cast_ringChar
    (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) X)
  rw [tateTwistSheafOneReductionMap, Functor.map_comp, Category.assoc, hn]
  infer_instance

omit [HasInvertibleExponent Λ' X] [NeZero (ringChar Λ')] in
/-- `tateTwistSheafOneReductionMap` is the adjoint of the change of coefficients of the Tate
sheaves `Λ_X(1) ⟶ Res (μ_{n'} ⊗ Λ')`. -/
lemma tateTwistSheafOneReductionMap_eq :
    tateTwistSheafOneReductionMap X e he (ρ := ρ) =
      ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _).symm
        ((tateTwistSheafOneIso X Λ).hom ≫ (extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _) := by
  rw [tateTwistSheafOneReductionMap, ← homEquiv_symm_extendScalarsChangeMap_app,
    ← Adjunction.homEquiv_naturality_left_symm, Category.assoc]

/-- `tateTwistObjectOneChangeMap` through the unit of the extension of scalars along `ρ` and the
isomorphism `tateTwistSheafOneReductionMap`. -/
lemma tateTwistObjectOneChangeMap_eq_unit :
    tateTwistObjectOneChangeMap ρ X e he =
    ((tateTwistObjectIsoSingleFunctor Λ X 1).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
          ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app
            (tateTwistSheaf Λ X 1)) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
          0).inv.app ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj (tateTwistSheaf Λ X 1))) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((DerivedCategory.singleFunctor _ 0).mapIso
            (asIso (tateTwistSheafOneReductionMap X e he (ρ := ρ))) ≪≫
          (tateTwistObjectOneIso X Λ').symm).hom := by
  have hu : (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app _ ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
        (tateTwistSheafOneReductionMap X e he (ρ := ρ)) =
      (tateTwistSheafOneIso X Λ).hom ≫ (extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
        (extendScalarsChangeMap ρ X).app _ := by
    rw [tateTwistSheafOneReductionMap_eq]
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  exact comp_map_eq_of_unit_comp_eq _ _ (tateTwistObjectOneChangeMap_eq ρ X e he) rfl hu
    (singleFunctor_map_restrictScalars_map_comp_singleFunctorRestrictScalarsIso_hom ρ X
      (tateTwistSheafOneReductionMap X e he (ρ := ρ))) rfl

include hρ ha in
/-- **The reduction of the Tate twist `Λ(1)`**: the change of coefficients
`Λ_X(1) ⟶ Res Λ'_X(1)` (`tateTwistObjectOneChangeMap`, the `e`-th power map) exhibits
`Λ'_X(1)` as the derived extension of scalars of `Λ_X(1)`. -/
theorem isDerivedBaseChange_tateTwistObjectOneChangeMap :
    Sheaf.IsDerivedBaseChange (tateTwistObjectOneChangeMap ρ X e he) := by
  have hη := isDerivedBaseChange_singleFunctor_map_unit hρ ha X (flat_tateTwistSheaf Λ X 1)
  rw [tateTwistObjectOneChangeMap_eq_unit]
  exact (hη.of_iso (tateTwistObjectIsoSingleFunctor Λ X 1)).comp_map_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (tateTwistSheafOneReductionMap X e he (ρ := ρ))) ≪≫ (tateTwistObjectOneIso X Λ').symm)

include hρ ha in
/-- **The reduction of the Tate twist `Λ(1)`**: the adjoint `Ψ(Λ_X(1)) ⟶ Λ'_X(1)` of the change
of coefficients `tateTwistObjectOneChangeMap` (the `e`-th power map) is an isomorphism. -/
theorem isIso_homEquiv_symm_tateTwistObjectOneChangeMap :
    IsIso (((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm
      (tateTwistObjectOneChangeMap ρ X e he)) :=
  (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hρ ha X _).isIso
    (isDerivedBaseChange_tateTwistObjectOneChangeMap hρ ha X e he) _
    ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _))

end AlgebraicGeometry.Etale
